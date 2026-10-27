'use strict';

/* global parseDump */

const $ = id => document.getElementById(id);

const ESC = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' };
const esc = s => String(s).replace(/[&<>"]/g, c => ESC[c]);
const hex = n => '0x' + n.toString(16).toUpperCase();
const fmtInt = n => n.toLocaleString('ru-RU');

function store(key, value) {
  try {
    if (value === undefined) return localStorage.getItem(key);
    localStorage.setItem(key, value);
  } catch (e) { /* хранилище недоступно: работаем без него */ }
  return null;
}

// ---------------------------------------------------------------------------
// Имена типов
// ---------------------------------------------------------------------------

function splitTop(s, sep) {
  const out = [];
  let depth = 0, start = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s[i];
    if (c === '<' || c === '(' || c === '[') depth++;
    else if (c === '>' || c === ')' || c === ']') { if (depth > 0) depth--; }
    else if (c === sep && depth === 0) { out.push(s.slice(start, i)); start = i + 1; }
  }
  out.push(s.slice(start));
  return out;
}

function genericStart(seg) {
  if (!seg.endsWith('>')) return -1;
  let depth = 0;
  for (let i = seg.length - 1; i >= 0; i--) {
    if (seg[i] === '>') depth++;
    else if (seg[i] === '<' && --depth === 0) return i > 0 ? i : -1;
  }
  return -1;
}

const stripGeneric = seg => { const i = genericStart(seg); return i > 0 ? seg.slice(0, i) : seg; };
const arityOf = seg => { const i = genericStart(seg); return i > 0 ? splitTop(seg.slice(i + 1, -1), ',').length : 0; };
const typeKeyOf = name => splitTop(name.trim(), '.').map(s => stripGeneric(s.trim())).join('.');
const lastSeg = name => { const p = splitTop(name, '.'); return p[p.length - 1]; };

// ---------------------------------------------------------------------------
// Загруженные дампы
// ---------------------------------------------------------------------------

const docs = new Map();
let nextDocId = 1;

const KIND_ORDER = { ctor: 0, method: 1, property: 2, event: 3, field: 4, const: 5 };
const KIND_LABEL = { class: 'class', struct: 'struct', interface: 'interface', enum: 'enum', delegate: 'delegate' };

function buildDoc(name, text, r, ms) {
  const doc = {
    id: nextDocId++,
    name,
    text,
    lineStarts: r.lineStarts,
    lineCount: r.lineCount,
    images: r.images.length ? r.images : [{ index: 0, name: name, first: 0 }],
    types: r.types,
    parseMs: ms,
  };

  doc.byKey = new Map();     // "Outer.Inner" -> [id]
  doc.byFull = new Map();    // "Ns.Outer.Inner" -> [id]
  doc.bySimple = new Map();  // "Inner" -> [id]
  doc.derived = new Map();   // id -> [id]
  doc.nested = new Map();    // id -> [id]
  doc.imageNs = doc.images.map(() => new Map()); // ns -> [top-level ids]
  let memberCount = 0;

  const push = (map, k, v) => { const a = map.get(k); if (a) a.push(v); else map.set(k, [v]); };
  for (const t of doc.types) {
    t.arity = arityOf(t.short);
    push(doc.byKey, t.key, t.id);
    push(doc.byFull, t.ns ? t.ns + '.' + t.key : t.key, t.id);
    push(doc.bySimple, t.simple, t.id);
    memberCount += t.members.length;
    t.members.forEach((m, i) => { m.idx = i; });
    if (t.parent >= 0) push(doc.nested, t.parent, t.id);
    else push(doc.imageNs[t.image] || doc.imageNs[0], t.ns, t.id);
  }
  doc.memberCount = memberCount;

  for (const t of doc.types) {
    t.baseIds = t.bases.map(b => resolveType(doc, typeKeyOf(b), t, arityOf(lastSeg(b))));
    for (const b of t.baseIds) if (b >= 0) push(doc.derived, b, t.id);
  }

  const byName = (a, b) => { const x = doc.types[a].name.toLowerCase(), y = doc.types[b].name.toLowerCase(); return x < y ? -1 : x > y ? 1 : 0; };
  for (const m of doc.imageNs) for (const ids of m.values()) ids.sort(byName);
  for (const ids of doc.nested.values()) ids.sort(byName);
  for (const ids of doc.derived.values()) ids.sort(byName);
  return doc;
}

// Выбор типа по имени из ссылки в коде; ctx — тип, в котором встретилась ссылка.
function resolveType(doc, key, ctx, arity) {
  let cands = doc.byFull.get(key) || doc.byKey.get(key);
  if (!cands && key.indexOf('.') > 0) {
    // "System.Collections.Generic.List" без точного совпадения — пробуем хвост.
    const parts = key.split('.');
    for (let i = 1; i < parts.length && !cands; i++) cands = doc.byKey.get(parts.slice(i).join('.'));
  }
  if (!cands) {
    // Короткое имя вложенного типа внутри его же родителя.
    const s = doc.bySimple.get(key);
    if (s && ctx) {
      const f = s.filter(id => isAncestor(doc, doc.types[id].parent, ctx));
      if (f.length) cands = f;
    }
  }
  if (!cands) return -1;
  if (cands.length === 1) return cands[0];
  let best = cands[0], bestScore = -1;
  for (const id of cands) {
    const t = doc.types[id];
    let score = 0;
    if (arity !== undefined && (t.arity > 0) === (arity > 0)) score += t.arity === arity ? 8 : 4;
    if (ctx) {
      if (t.ns === ctx.ns) score += 2;
      if (t.image === ctx.image) score += 1;
      if (t.parent >= 0 && isAncestor(doc, t.parent, ctx)) score += 16;
    }
    if (score > bestScore) { best = id; bestScore = score; }
  }
  return best;
}

function isAncestor(doc, id, t) {
  for (let c = t; c; c = c.parent >= 0 ? doc.types[c.parent] : null) if (c.id === id) return true;
  return false;
}

function line(doc, i) {
  const s = doc.lineStarts[i];
  const e = i + 1 < doc.lineCount ? doc.lineStarts[i + 1] - 1 : doc.text.length;
  let str = doc.text.slice(s, e);
  if (str.charCodeAt(str.length - 1) === 13) str = str.slice(0, -1);
  return str;
}

// ---------------------------------------------------------------------------
// Загрузка файлов
// ---------------------------------------------------------------------------

let workerUrl = null;
function getWorkerUrl() {
  if (!workerUrl) {
    const src = parseDump.toString() + `
self.onmessage = async e => {
  try {
    const text = await e.data.file.text();
    const t0 = performance.now();
    const r = parseDump(text, p => self.postMessage({ type: 'progress', p }));
    self.postMessage({ type: 'done', r, text, ms: performance.now() - t0 }, [r.lineStarts.buffer]);
  } catch (err) {
    self.postMessage({ type: 'error', message: String(err && err.message || err) });
  }
};`;
    workerUrl = URL.createObjectURL(new Blob([src], { type: 'text/javascript' }));
  }
  return workerUrl;
}

function parseInWorker(file, onProgress) {
  return new Promise((resolve, reject) => {
    let w;
    try { w = new Worker(getWorkerUrl()); } catch (e) { reject(e); return; }
    w.onmessage = e => {
      const d = e.data;
      if (d.type === 'progress') onProgress(d.p);
      else { w.terminate(); d.type === 'done' ? resolve(d) : reject(new Error(d.message)); }
    };
    w.onerror = e => { w.terminate(); reject(new Error(e.message || 'worker error')); };
    w.postMessage({ file });
  });
}

async function parseOnMainThread(file) {
  const text = await file.text();
  const t0 = performance.now();
  const r = parseDump(text);
  return { r, text, ms: performance.now() - t0 };
}

async function openFiles(files) {
  for (const file of files) {
    showLoading(`Разбор ${file.name}…`, 0);
    try {
      let res;
      try {
        res = await parseInWorker(file, p => showLoading(`Разбор ${file.name}…`, p));
      } catch (e) {
        showLoading(`Разбор ${file.name}…`, .5);
        res = await parseOnMainThread(file);
      }
      if (!res.r.types.length) {
        alert(`В файле ${file.name} не найдено ни одного типа. Ожидается dump.cs из Il2CppDumper.`);
        continue;
      }
      const doc = buildDoc(file.name, res.text, res.r, res.ms);
      docs.set(doc.id, doc);
      search.invalidate();
      tree.addDoc(doc);
      updateStatus(doc);
    } catch (e) {
      alert(`Не удалось открыть ${file.name}: ${e.message}`);
    }
  }
  hideLoading();
  updateWelcome();
}

function showLoading(text, p) {
  $('loading').hidden = false;
  $('loadingText').textContent = text;
  $('loadingBar').style.width = Math.round(p * 100) + '%';
}
function hideLoading() { $('loading').hidden = true; }

function updateStatus(doc) {
  if (!doc) { $('status').textContent = docs.size ? `Открыто дампов: ${docs.size}` : 'Готово'; return; }
  $('status').textContent = `${doc.name}: ${fmtInt(doc.types.length)} типов, ${fmtInt(doc.memberCount)} членов, ` +
    `${fmtInt(doc.images.length)} сборок, ${fmtInt(doc.lineCount)} строк · разобран за ${(doc.parseMs / 1000).toFixed(2)} с`;
}

function updateWelcome() {
  $('welcome').hidden = tabs.list.length > 0;
  $('welcomeHint').hidden = docs.size > 0;
  $('welcomeLoaded').hidden = docs.size === 0;
}

// ---------------------------------------------------------------------------
// Иконки
// ---------------------------------------------------------------------------

const ICONS = {
  asm: '<svg viewBox="0 0 16 16"><rect x="2" y="2" width="12" height="12" rx="1" fill="none" stroke="#c5c5c5"/><path d="M5 5h6M5 8h6M5 11h4" stroke="#c5c5c5"/></svg>',
  dump: '<svg viewBox="0 0 16 16"><path d="M3 1.5h7l3 3v10H3z" fill="none" stroke="#c5c5c5"/><path d="M10 1.5v3h3" fill="none" stroke="#c5c5c5"/><text x="8" y="12.5" font-size="6" text-anchor="middle" fill="#4ec9b0" font-family="monospace">C#</text></svg>',
  ns: '<svg viewBox="0 0 16 16"><text x="8" y="12" font-size="11" text-anchor="middle" fill="#c5c5c5" font-family="monospace">{}</text></svg>',
  class: '<svg viewBox="0 0 16 16"><path d="M8 2 13 5v6l-5 3-5-3V5z" fill="#e8ab53" stroke="#a46f22"/><path d="M8 8v6M8 8l5-3M8 8 3 5" stroke="#a46f22" fill="none"/></svg>',
  struct: '<svg viewBox="0 0 16 16"><rect x="2.5" y="3.5" width="11" height="9" fill="#3fa9e0" stroke="#1d6b9a"/><path d="M2.5 8h11M8 3.5v9" stroke="#1d6b9a"/></svg>',
  interface: '<svg viewBox="0 0 16 16"><circle cx="11" cy="8" r="3" fill="none" stroke="#3fa9e0" stroke-width="2"/><path d="M1.5 8H8" stroke="#3fa9e0" stroke-width="2"/></svg>',
  enum: '<svg viewBox="0 0 16 16"><rect x="2" y="3" width="8" height="6" fill="#e8ab53" stroke="#a46f22"/><rect x="6" y="7" width="8" height="6" fill="#e8ab53" stroke="#a46f22"/></svg>',
  delegate: '<svg viewBox="0 0 16 16"><path d="M3 4h7l3 4-3 4H3z" fill="#b180d7" stroke="#7a4f9a"/></svg>',
  method: '<svg viewBox="0 0 16 16"><path d="M8 2 13 5v6l-5 3-5-3V5z" fill="#b180d7" stroke="#6c3e8c"/><path d="M8 8v6M8 8l5-3M8 8 3 5" stroke="#6c3e8c" fill="none"/></svg>',
  ctor: '<svg viewBox="0 0 16 16"><path d="M8 2 13 5v6l-5 3-5-3V5z" fill="#b180d7" stroke="#6c3e8c"/><circle cx="8" cy="8" r="2" fill="#fff"/></svg>',
  field: '<svg viewBox="0 0 16 16"><path d="M8 3 13 6v4l-5 3-5-3V6z" fill="#3fa9e0" stroke="#1d6b9a"/></svg>',
  const: '<svg viewBox="0 0 16 16"><rect x="3" y="5" width="10" height="6" fill="#9e9e9e" stroke="#5f5f5f"/><path d="M5 8h6" stroke="#fff"/></svg>',
  property: '<svg viewBox="0 0 16 16"><path d="M3 13 9 7M9.5 2.5a3.5 3.5 0 1 0 4 4l-2 .2-2-2z" fill="none" stroke="#c5c5c5" stroke-width="1.6"/></svg>',
  event: '<svg viewBox="0 0 16 16"><path d="M9 1 3 9h4l-1 6 6-8H8z" fill="#e8ab53" stroke="#a46f22" stroke-width=".8"/></svg>',
  base: '<svg viewBox="0 0 16 16"><path d="M8 13V4M4 8l4-4 4 4" fill="none" stroke="#c5c5c5" stroke-width="1.6"/></svg>',
  derived: '<svg viewBox="0 0 16 16"><path d="M8 3v9M4 8l4 4 4-4" fill="none" stroke="#c5c5c5" stroke-width="1.6"/></svg>',
  missing: '<svg viewBox="0 0 16 16"><path d="M8 2 13 5v6l-5 3-5-3V5z" fill="none" stroke="#8a8a8a" stroke-dasharray="2 1.5"/></svg>',
};

// ---------------------------------------------------------------------------
// Подписи узлов
// ---------------------------------------------------------------------------

function typeLabel(t, full) {
  return `<span class="k-${t.kind}">${esc(full ? t.name : t.short)}</span>`;
}

function memberLabel(m) {
  const name = `<span class="k-${m.kind}">${esc(m.name)}</span>`;
  if (m.kind === 'method' || m.kind === 'ctor') {
    return `${name}(${m.params.map(esc).join(', ')}) <span class="dim">:</span> ${esc(m.type)}`;
  }
  if (m.kind === 'const' && m.value !== null) return `${name} <span class="dim">:</span> ${esc(m.type)} <span class="dim">= ${esc(m.value.length > 40 ? m.value.slice(0, 40) + '…' : m.value)}</span>`;
  return `${name} <span class="dim">:</span> ${esc(m.type)}`;
}

function memberTitle(t, m) {
  let s = `${m.mods.join(' ')} ${m.type} ${t.name}.${m.name}`;
  if (m.params) s += `(${m.params.join(', ')})`;
  if (m.rva >= 0) s += `\nRVA: ${hex(m.rva)}  Offset: ${hex(m.off)}  VA: ${hex(m.va)}`;
  if (m.slot >= 0) s += `\nSlot: ${m.slot}`;
  if (m.fieldOffset >= 0) s += `\nOffset: ${hex(m.fieldOffset)}`;
  return s;
}

function typeTitle(doc, t) {
  return `${t.mods.join(' ')} ${t.kind} ${t.ns ? t.ns + '.' : ''}${t.name}\n` +
    `${doc.images[t.image].name} · TypeDefIndex: ${t.index}` + (t.bases.length ? `\n: ${t.bases.join(', ')}` : '');
}

// ---------------------------------------------------------------------------
// Дерево
// ---------------------------------------------------------------------------

class TreeNode {
  constructor(o) {
    Object.assign(this, o);   // key, icon, label, title, children(), activate(e), closable
    this.parent = null;
    this.kids = null;
    this.li = null;
  }

  render(depth) {
    this.depth = depth;
    const li = document.createElement('li');
    const row = document.createElement('div');
    row.className = 'row';
    row.style.paddingLeft = (depth * 16 + 2) + 'px';
    row.innerHTML = `<span class="twisty${this.children ? ' has' : ''}"></span><span class="ic">${ICONS[this.icon] || ''}</span>` +
      `<span class="lbl">${this.label}</span>` + (this.closable ? '<span class="close" title="Закрыть дамп">&#215;</span>' : '');
    if (this.title) row.title = this.title;
    row._node = this;
    li.appendChild(row);
    this.li = li;
    this.row = row;
    return li;
  }

  ensureKids() {
    if (this.kids || !this.children) return;
    this.kids = this.children();
    const ul = document.createElement('ul');
    const frag = document.createDocumentFragment();
    for (const k of this.kids) { k.parent = this; frag.appendChild(k.render(this.depth + 1)); }
    ul.appendChild(frag);
    this.li.appendChild(ul);
    if (!this.kids.length) this.row.firstChild.classList.remove('has');
  }

  get open() { return this.li.classList.contains('open'); }

  setOpen(v) {
    if (!this.children) return;
    if (v) this.ensureKids();
    this.li.classList.toggle('open', v);
  }

  find(key) {
    this.ensureKids();
    return (this.kids || []).find(k => k.key === key) || null;
  }
}

const tree = {
  el: $('tree'),
  ul: document.createElement('ul'),
  roots: [],
  selected: null,

  init() {
    this.el.appendChild(this.ul);
    this.el.addEventListener('click', e => {
      const row = e.target.closest('.row');
      if (!row) return;
      const node = row._node;
      if (e.target.classList.contains('close')) { closeDoc(node.doc); return; }
      if (e.target.classList.contains('twisty')) { node.setOpen(!node.open); return; }
      this.select(node, false);
      if (node.activate) node.activate(e.ctrlKey || e.metaKey);
    });
    this.el.addEventListener('dblclick', e => {
      const row = e.target.closest('.row');
      if (row && !e.target.classList.contains('twisty')) row._node.setOpen(!row._node.open);
    });
    this.el.addEventListener('auxclick', e => {
      const row = e.target.closest('.row');
      if (e.button === 1 && row && row._node.activate) { e.preventDefault(); row._node.activate(true); }
    });
    this.el.addEventListener('keydown', e => this.onKey(e));
  },

  addDoc(doc) {
    const node = docNode(doc);
    this.roots.push(node);
    this.ul.appendChild(node.render(0));
    node.setOpen(true);
    if (doc.images.length === 1) node.kids[0].setOpen(true);
  },

  removeDoc(doc) {
    const i = this.roots.findIndex(n => n.doc === doc);
    if (i < 0) return;
    if (this.selected && this.selected.doc === doc) this.selected = null;
    this.roots[i].li.remove();
    this.roots.splice(i, 1);
  },

  select(node, scroll) {
    if (this.selected && this.selected.row) this.selected.row.classList.remove('sel');
    this.selected = node;
    if (!node) return;
    node.row.classList.add('sel');
    if (scroll) node.row.scrollIntoView({ block: 'nearest' });
  },

  visibleRows() {
    return Array.from(this.el.querySelectorAll('.row')).filter(r => r.offsetParent !== null);
  },

  onKey(e) {
    const sel = this.selected;
    const move = delta => {
      const rows = this.visibleRows();
      let i = sel ? rows.indexOf(sel.row) : -1;
      i = Math.max(0, Math.min(rows.length - 1, i + delta));
      if (rows[i]) { const n = rows[i]._node; this.select(n, true); if (n.activate) n.activate(false, true); }
    };
    switch (e.key) {
      case 'ArrowDown': move(1); break;
      case 'ArrowUp': move(-1); break;
      case 'PageDown': move(20); break;
      case 'PageUp': move(-20); break;
      case 'ArrowRight':
        if (!sel) return;
        if (sel.children && !sel.open) sel.setOpen(true); else move(1);
        break;
      case 'ArrowLeft':
        if (!sel) return;
        if (sel.open) sel.setOpen(false);
        else if (sel.parent) { this.select(sel.parent, true); if (sel.parent.activate) sel.parent.activate(false, true); }
        break;
      case 'Enter':
        if (sel) { if (sel.children) sel.setOpen(!sel.open); if (sel.activate) sel.activate(e.ctrlKey); }
        break;
      default: return;
    }
    e.preventDefault();
  },

  // Раскрывает дерево до типа (и члена) и выделяет узел.
  reveal(doc, typeId, memberIdx) {
    const root = this.roots.find(n => n.doc === doc);
    if (!root) return;
    const t = doc.types[typeId];
    const chain = [];
    for (let c = t; c; c = c.parent >= 0 ? doc.types[c.parent] : null) chain.unshift(c);
    let node = root;
    const path = ['img:' + chain[0].image, 'ns:' + chain[0].ns].concat(chain.map(c => 'type:' + c.id));
    if (memberIdx !== undefined && memberIdx >= 0) path.push('mem:' + memberIdx);
    for (const key of path) {
      node.setOpen(true);
      const next = node.find(key);
      if (!next) break;
      node = next;
    }
    this.select(node, true);
  },
};

function docNode(doc) {
  return new TreeNode({
    doc, key: 'doc:' + doc.id, icon: 'dump', closable: true,
    label: `<span class="k-asm">${esc(doc.name)}</span>`,
    title: `${doc.name}\n${fmtInt(doc.types.length)} типов, ${fmtInt(doc.lineCount)} строк`,
    activate: (newTab, quiet) => { updateStatus(doc); if (!quiet) openView(fullFileView(doc), newTab); },
    children: () => doc.images.map((im, i) => imageNode(doc, i)),
  });
}

function imageNode(doc, i) {
  const im = doc.images[i];
  return new TreeNode({
    doc, key: 'img:' + i, icon: 'asm',
    label: `<span class="k-asm">${esc(im.name)}</span>`,
    title: `${im.name}\nImage ${im.index}, первый TypeDefIndex: ${im.first}`,
    activate: newTab => openView(imageView(doc, i), newTab),
    children: () => Array.from(doc.imageNs[i].keys()).sort((a, b) => a.localeCompare(b))
      .map(ns => nsNode(doc, i, ns)),
  });
}

function nsNode(doc, img, ns) {
  return new TreeNode({
    doc, key: 'ns:' + ns, icon: 'ns',
    label: `<span class="k-ns">${esc(ns || '-')}</span>`,
    activate: newTab => openView(namespaceView(doc, img, ns), newTab),
    children: () => doc.imageNs[img].get(ns).map(id => typeNode(doc, id)),
  });
}

function typeNode(doc, id, keyPrefix) {
  const t = doc.types[id];
  return new TreeNode({
    doc, key: (keyPrefix || 'type:') + id, icon: t.kind,
    label: typeLabel(t, t.parent < 0),
    title: typeTitle(doc, t),
    activate: newTab => openType(doc, id, -1, newTab, false),
    children: keyPrefix ? null : () => typeChildren(doc, t),
  });
}

function typeChildren(doc, t) {
  const out = [];
  if (t.bases.length) out.push(baseNode(doc, t));
  if (doc.derived.has(t.id)) out.push(derivedNode(doc, t));
  for (const id of doc.nested.get(t.id) || []) out.push(typeNode(doc, id));
  const members = t.members.slice().sort((a, b) =>
    (KIND_ORDER[a.kind] - KIND_ORDER[b.kind]) || (a.kind === 'const' ? a.idx - b.idx : a.name.localeCompare(b.name)) || a.idx - b.idx);
  for (const m of members) {
    out.push(new TreeNode({
      doc, key: 'mem:' + m.idx, icon: m.kind,
      label: memberLabel(m),
      title: memberTitle(t, m),
      activate: newTab => openType(doc, t.id, m.idx, newTab),
    }));
  }
  return out;
}

function baseNode(doc, t) {
  return new TreeNode({
    doc, key: 'bases', icon: 'base', label: 'Base Type and Interfaces',
    children: () => t.bases.map((b, i) => {
      const id = t.baseIds[i];
      if (id < 0) return new TreeNode({ doc, key: 'b' + i, icon: 'missing', label: `<span class="dim">${esc(b)}</span>`, title: 'Тип не найден в дампе' });
      const bt = doc.types[id];
      return new TreeNode({
        doc, key: 'b' + i, icon: bt.kind, label: `<span class="k-${bt.kind}">${esc(b)}</span>`, title: typeTitle(doc, bt),
        activate: newTab => openType(doc, id, -1, newTab, false),
        children: bt.bases.length ? () => [baseNode(doc, bt)] : null,
      });
    }),
  });
}

function derivedNode(doc, t) {
  return new TreeNode({
    doc, key: 'derived', icon: 'derived', label: 'Derived Types',
    children: () => doc.derived.get(t.id).map(id => {
      const dt = doc.types[id];
      return new TreeNode({
        doc, key: 'd' + id, icon: dt.kind, label: typeLabel(dt, true), title: typeTitle(doc, dt),
        activate: newTab => openType(doc, id, -1, newTab, false),
        children: doc.derived.has(id) ? () => [derivedNode(doc, dt)] : null,
      });
    }),
  });
}

function closeDoc(doc) {
  for (let i = tabs.list.length - 1; i >= 0; i--) if (tabs.list[i].view.doc === doc) tabs.close(i);
  tree.removeDoc(doc);
  docs.delete(doc.id);
  search.invalidate();
  updateStatus(null);
  updateWelcome();
}

// ---------------------------------------------------------------------------
// Представления: что показывать во вкладке
// ---------------------------------------------------------------------------

// view = { doc, id, title, tooltip, ctx (тип для разрешения имён), lines: Int32Array | null, virt: string[] | null,
//          typeId, memberLine }

function isGenericLine(s) {
  const t = s.trimStart();
  return t.startsWith('/* GenericInstMethod') || t.startsWith('|') || t === '*/';
}

function rangeLines(doc, from, to) {
  const showGeneric = $('optGeneric').checked;
  const out = new Int32Array(to - from + 1);
  let n = 0;
  for (let i = from; i <= to; i++) {
    if (!showGeneric) {
      const c = doc.text.charCodeAt(doc.lineStarts[i] + 1);
      if ((c === 47 || c === 124 || c === 42) && isGenericLine(line(doc, i))) continue; // '/', '|', '*'
    }
    out[n++] = i;
  }
  return out.subarray(0, n);
}

function typeView(doc, id) {
  const t = doc.types[id];
  return {
    doc, id: `t:${doc.id}:${id}`, typeId: id, ctx: t,
    title: t.short, tooltip: typeTitle(doc, t),
    build: () => rangeLines(doc, t.start, t.end),
  };
}

function fullFileView(doc) {
  return {
    doc, id: `f:${doc.id}`, title: doc.name, tooltip: doc.name,
    build: () => rangeLines(doc, 0, doc.lineCount - 1),
  };
}

function imageView(doc, i) {
  const im = doc.images[i];
  return {
    doc, id: `i:${doc.id}:${i}`, title: im.name, tooltip: im.name, noLinks: true,
    build: () => {
      const v = [`// ${im.name}`, `// Image ${im.index}, первый TypeDefIndex: ${im.first}`, ''];
      const nss = Array.from(doc.imageNs[i].keys()).sort((a, b) => a.localeCompare(b));
      let count = 0;
      for (const ns of nss) count += doc.imageNs[i].get(ns).length;
      v.push(`// Пространств имён: ${nss.length}, типов верхнего уровня: ${count}`, '');
      for (const ns of nss) v.push(`namespace ${ns || '-'} // ${doc.imageNs[i].get(ns).length}`);
      return v;
    },
  };
}

function namespaceView(doc, img, ns) {
  const ids = doc.imageNs[img].get(ns);
  return {
    doc, id: `n:${doc.id}:${img}:${ns}`, title: ns || '-', tooltip: `${ns || '-'} · ${doc.images[img].name}`,
    ctx: { ns, image: img, parent: -1, id: -1 },
    build: () => {
      const v = [`// Namespace: ${ns}`, `// ${doc.images[img].name}, типов: ${ids.length}`, ''];
      for (const id of ids) {
        const t = doc.types[id];
        v.push(`${t.mods.join(' ')} ${t.kind} ${t.name}${t.bases.length ? ' : ' + t.bases.join(', ') : ''} // TypeDefIndex: ${t.index}`);
      }
      return v;
    },
  };
}

// ---------------------------------------------------------------------------
// Подсветка
// ---------------------------------------------------------------------------

const KEYWORDS = new Set(('abstract as base bool break byte case catch char checked class const continue decimal default delegate do double else enum event explicit extern false finally fixed float for foreach goto if implicit in int interface internal is lock long namespace new null object operator out override params private protected public readonly ref return sbyte sealed short sizeof stackalloc static string struct switch this throw true try typeof uint ulong unchecked unsafe ushort using virtual void volatile while get set add remove var').split(' '));
const ALIASES = { string: 'String', object: 'Object', int: 'Int32', uint: 'UInt32', long: 'Int64', ulong: 'UInt64', short: 'Int16', ushort: 'UInt16', byte: 'Byte', sbyte: 'SByte', bool: 'Boolean', char: 'Char', float: 'Single', double: 'Double', decimal: 'Decimal', void: 'Void' };

const TOKEN_RE = /(\/\/.*$)|("(?:[^"\\]|\\.)*"?)|('(?:[^'\\]|\\.)*'?)|(-?0x[0-9A-Fa-f]+\b|-?\b\d+(?:\.\d+)?(?:[eE][+-]?\d+)?[fFdDmMuUlL]*\b)|((?<![\w>])<[\w|$]*>[\w$`]*)|([A-Za-z_@][\w`]*(?:\.[A-Za-z_][\w`]*)*)|(\s+)|([^\s\w"'/]+|\/)|(.)/g;

function highlight(text, doc, ctx) {
  const trimmed = text.trimStart();
  if (trimmed.startsWith('//') || trimmed.startsWith('/*') || trimmed.startsWith('|') || trimmed.startsWith('*/')) {
    return commentHtml(text);
  }
  let out = '';
  TOKEN_RE.lastIndex = 0;
  let m;
  while ((m = TOKEN_RE.exec(text))) {
    const s = m[0];
    if (m[1]) out += commentHtml(s);
    else if (m[2] || m[3]) out += `<span class="t-str">${esc(s)}</span>`;
    else if (m[4]) out += `<span class="t-num">${esc(s)}</span>`;
    else if (m[5]) out += esc(s);
    else if (m[6]) out += identHtml(s, text, TOKEN_RE.lastIndex, doc, ctx);
    else out += esc(s);
  }
  return out;
}

function commentHtml(s) {
  return `<span class="t-cm">${esc(s).replace(/\b(0x[0-9A-F]+)\b/g, '<span class="t-addr">$1</span>')}</span>`;
}

function typeRef(doc, id, text) {
  const t = doc.types[id];
  return `<span class="k-${t.kind} tref" data-t="${id}" title="${esc((t.ns ? t.ns + '.' : '') + t.name + ' · ' + doc.images[t.image].name)}">${esc(text)}</span>`;
}

function identHtml(s, text, end, doc, ctx) {
  if (!doc) return KEYWORDS.has(s) ? `<span class="t-kw">${s}</span>` : esc(s);
  const generic = text[end] === '<';
  const isCall = /^\s*\(/.test(text.slice(end, end + 4));
  if (s.indexOf('.') < 0) {
    if (KEYWORDS.has(s)) {
      const alias = ALIASES[s];
      if (alias) {
        const id = resolveType(doc, 'System.' + alias);
        if (id >= 0) return `<span class="t-kw tref" data-t="${id}">${s}</span>`;
      }
      return `<span class="t-kw">${s}</span>`;
    }
    if (!isCall) {
      const id = resolveType(doc, s, ctx, generic ? 1 : 0);
      if (id >= 0) return typeRef(doc, id, s);
    }
    return isCall ? `<span class="t-m">${esc(s)}</span>` : esc(s);
  }
  // Цепочка с точками: целиком тип ("Outer.Inner", "System.Text.StringBuilder") или по частям.
  if (!isCall) {
    const id = resolveType(doc, s, ctx, generic ? 1 : 0);
    if (id >= 0) return typeRef(doc, id, s);
  }
  const parts = s.split('.');
  return parts.map((p, i) => {
    const last = i === parts.length - 1;
    if (last && isCall) return `<span class="t-m">${esc(p)}</span>`;
    const id = /^[A-Z]/.test(p) ? resolveType(doc, p, ctx, last && generic ? 1 : 0) : -1;
    return id >= 0 ? typeRef(doc, id, p) : esc(p);
  }).join('.');
}

// ---------------------------------------------------------------------------
// Просмотр кода с виртуальной прокруткой
// ---------------------------------------------------------------------------

const MAX_SCROLL_PX = 8e6;

const codeView = {
  el: $('code'),
  spacer: $('codeSpacer'),
  linesEl: $('codeLines'),
  lh: 18,
  charW: 7.2,
  tab: null,
  raf: 0,

  init() {
    const probe = document.createElement('span');
    probe.style.cssText = 'position:absolute;visibility:hidden;white-space:pre;font:13px var(--mono)';
    probe.textContent = 'x'.repeat(100);
    this.el.appendChild(probe);
    this.charW = probe.getBoundingClientRect().width / 100 || 7.2;
    probe.remove();
    this.lh = parseFloat(getComputedStyle(document.documentElement).getPropertyValue('--line-h')) || 18;

    this.el.addEventListener('scroll', () => this.schedule());
    new ResizeObserver(() => this.schedule()).observe(this.el);
    this.el.addEventListener('click', e => {
      const ref = e.target.closest('.tref');
      if (ref && this.tab) openType(this.tab.view.doc, +ref.dataset.t, -1, e.ctrlKey || e.metaKey, true);
    });
    this.el.addEventListener('auxclick', e => {
      const ref = e.target.closest('.tref');
      if (e.button === 1 && ref && this.tab) { e.preventDefault(); openType(this.tab.view.doc, +ref.dataset.t, -1, true, true); }
    });
  },

  count() { const t = this.tab; return t ? (t.lines ? t.lines.length : t.virt.length) : 0; },

  show(tab) {
    if (this.tab && this.tab !== tab) this.tab.scrollLine = this.firstLine();
    this.tab = tab;
    if (!tab) { this.linesEl.innerHTML = ''; this.spacer.style.height = '0'; return; }
    const doc = tab.view.doc;
    const n = this.count();
    let maxChars = 0;
    if (tab.lines) {
      for (let i = 0; i < n; i++) {
        const a = tab.lines[i];
        const l = (a + 1 < doc.lineCount ? doc.lineStarts[a + 1] : doc.text.length) - doc.lineStarts[a];
        if (l > maxChars) maxChars = l;
      }
    } else {
      for (const s of tab.virt) if (s.length > maxChars) maxChars = s.length;
    }
    const lastNo = tab.lines ? (n ? tab.lines[n - 1] + 1 : 1) : n;
    this.gutterChars = Math.max(4, String(lastNo).length);
    const gutterW = (this.gutterChars + 2) * this.charW + 23;
    const width = Math.ceil(gutterW + (maxChars + 12) * this.charW + 24);
    this.spacer.style.width = width + 'px';
    this.linesEl.style.width = width + 'px';
    this.spacer.style.height = Math.min(n * this.lh, MAX_SCROLL_PX) + 'px';
    this.scrollToLine(tab.scrollLine || 0, false);
    this.render();
  },

  geometry() {
    const n = this.count();
    const viewH = this.el.clientHeight;
    const visible = viewH / this.lh;
    const maxScroll = Math.max(0, Math.min(n * this.lh, MAX_SCROLL_PX) - viewH);
    const maxFirst = Math.max(0, n - visible);
    return { n, viewH, visible, maxScroll, maxFirst };
  },

  firstLine() {
    const g = this.geometry();
    return g.maxScroll > 0 ? this.el.scrollTop / g.maxScroll * g.maxFirst : 0;
  },

  scrollToLine(i, center) {
    const g = this.geometry();
    let first = center ? i - g.visible / 2 + 1 : i;
    first = Math.max(0, Math.min(g.maxFirst, first));
    this.el.scrollTop = g.maxFirst > 0 ? first / g.maxFirst * g.maxScroll : 0;
  },

  schedule() {
    if (!this.raf) this.raf = requestAnimationFrame(() => { this.raf = 0; this.render(); });
  },

  render() {
    const tab = this.tab;
    if (!tab) return;
    const g = this.geometry();
    const firstF = this.firstLine();
    const first = Math.max(0, Math.floor(firstF) - 2);
    const last = Math.min(g.n, Math.ceil(firstF + g.visible) + 2);
    const top = this.el.scrollTop - (firstF - first) * this.lh;
    const doc = tab.view.doc;
    const ctx = tab.view.ctx || null;
    let html = '';
    for (let i = first; i < last; i++) {
      const abs = tab.lines ? tab.lines[i] : -1;
      const text = tab.lines ? line(doc, abs) : tab.virt[i];
      const no = tab.lines ? abs + 1 : i + 1;
      const cls = tab.hl === i ? ' hl' + (tab.flash ? ' flash' : '') : '';
      html += `<div class="ln${cls}"><span class="gn" style="width:${(this.gutterChars + 2) * this.charW + 12}px">${no}</span>` +
        `<span class="tx">${highlight(text, tab.view.noLinks ? null : doc, ctx)}</span></div>`;
    }
    tab.flash = false;
    this.linesEl.style.transform = `translateY(${Math.max(0, top)}px)`;
    this.linesEl.innerHTML = html;
  },

};

// Индекс строки во вкладке по абсолютному номеру строки файла (или ближайший следующий).
function indexIn(lines, abs) {
  if (!lines || !lines.length) return 0;
  let lo = 0, hi = lines.length - 1;
  while (lo <= hi) {
    const mid = (lo + hi) >> 1;
    if (lines[mid] < abs) lo = mid + 1; else if (lines[mid] > abs) hi = mid - 1; else return mid;
  }
  return Math.min(lo, lines.length - 1);
}

// ---------------------------------------------------------------------------
// Вкладки и история
// ---------------------------------------------------------------------------

const tabs = {
  el: $('tabs'),
  list: [],
  active: -1,

  init() {
    this.el.addEventListener('mousedown', e => {
      const el = e.target.closest('.tab');
      if (!el) return;
      const i = +el.dataset.i;
      if (e.button === 1 || e.target.classList.contains('x')) { e.preventDefault(); this.close(i); }
      else if (e.button === 0) this.activate(i);
    });
  },

  current() { return this.list[this.active] || null; },

  open(view, newTab) {
    let tab = this.current();
    if (!tab || newTab) {
      tab = { view: null, back: [], fwd: [] };
      this.list.push(tab);
      this.active = this.list.length - 1;
    } else if (tab.view) {
      tab.back.push(this.snapshot(tab));
      tab.fwd = [];
    }
    this.load(tab, view);
    return tab;
  },

  snapshot(tab) {
    if (tab === codeView.tab) tab.scrollLine = codeView.firstLine();
    return { view: tab.view, scrollLine: tab.scrollLine, hl: tab.hl };
  },

  load(tab, view, state) {
    tab.view = view;
    const built = view.build();
    tab.lines = built instanceof Int32Array ? built : null;
    tab.virt = built instanceof Int32Array ? null : built;
    tab.hl = state ? state.hl : -1;
    tab.scrollLine = state ? state.scrollLine : 0;
    this.render();
    codeView.show(tab);
    updateWelcome();
    updateNavButtons();
  },

  // Перестраивает вкладку (например, после переключения GenericInstMethod), сохраняя позицию.
  reload(tab) {
    if (!tab.lines) return;
    const absHl = tab.hl >= 0 ? tab.lines[tab.hl] : -1;
    const absTop = tab.lines[Math.floor(codeView.firstLine())] || 0;
    tab.lines = tab.view.build();
    tab.hl = absHl >= 0 ? indexIn(tab.lines, absHl) : -1;
    tab.scrollLine = indexIn(tab.lines, absTop);
    codeView.show(tab);
  },

  activate(i) {
    if (i === this.active) return;
    if (this.current()) this.current().scrollLine = codeView.firstLine();
    this.active = i;
    this.render();
    codeView.show(this.current());
    updateNavButtons();
    const v = this.current().view;
    if (v.typeId !== undefined) tree.reveal(v.doc, v.typeId);
  },

  close(i) {
    if (i < 0 || i >= this.list.length) return;
    const wasActive = i === this.active;
    this.list.splice(i, 1);
    if (this.active > i || (wasActive && this.active >= this.list.length)) this.active--;
    if (wasActive) { codeView.tab = null; codeView.show(this.current()); }
    this.render();
    updateWelcome();
    updateNavButtons();
  },

  render() {
    this.el.innerHTML = this.list.map((t, i) =>
      `<div class="tab${i === this.active ? ' active' : ''}" data-i="${i}" title="${esc(t.view.tooltip || t.view.title)}">` +
      `<span>${esc(t.view.title)}</span><span class="x">&#215;</span></div>`).join('');
    const a = this.el.children[this.active];
    if (a) a.scrollIntoView({ block: 'nearest', inline: 'nearest' });
  },

  go(dir) {
    const tab = this.current();
    if (!tab) return;
    const from = dir < 0 ? tab.back : tab.fwd;
    const to = dir < 0 ? tab.fwd : tab.back;
    if (!from.length) return;
    to.push(this.snapshot(tab));
    const st = from.pop();
    this.load(tab, st.view, st);
    if (st.view.typeId !== undefined) tree.reveal(st.view.doc, st.view.typeId);
  },
};

function updateNavButtons() {
  const t = tabs.current();
  $('btnBack').disabled = !t || !t.back.length;
  $('btnForward').disabled = !t || !t.fwd.length;
}

function openView(view, newTab) {
  const cur = tabs.current();
  if (!newTab && cur && cur.view && cur.view.id === view.id) return cur;
  return tabs.open(view, newTab);
}

// Открывает тип; memberIdx >= 0 — подсветить член, line — подсветить конкретную строку файла.
function openType(doc, typeId, memberIdx, newTab, reveal, line) {
  const tab = openView(typeView(doc, typeId), newTab);
  const t = doc.types[typeId];
  const abs = line !== undefined ? line : memberIdx >= 0 ? t.members[memberIdx].line : t.decl;
  const i = indexIn(tab.lines, abs);
  tab.hl = memberIdx >= 0 || line !== undefined ? i : -1;
  tab.flash = tab.hl >= 0;
  codeView.scrollToLine(i, memberIdx >= 0 || line !== undefined);
  codeView.render();
  if (reveal) tree.reveal(doc, typeId, memberIdx);
  updateStatus(doc);
}

// ---------------------------------------------------------------------------
// Поиск
// ---------------------------------------------------------------------------

const MAX_RESULTS = 1000;

const search = {
  pane: $('searchPane'),
  input: $('searchInput'),
  kind: $('searchKind'),
  results: $('searchResults'),
  count: $('searchCount'),
  timer: 0,
  items: [],
  sel: -1,
  addrIndex: null,

  init() {
    this.input.addEventListener('input', () => this.schedule());
    this.kind.addEventListener('change', () => this.run());
    $('searchCase').addEventListener('change', () => this.run());
    $('searchClose').addEventListener('click', () => this.hide());
    this.input.addEventListener('keydown', e => {
      if (e.key === 'ArrowDown') { this.move(1); e.preventDefault(); }
      else if (e.key === 'ArrowUp') { this.move(-1); e.preventDefault(); }
      else if (e.key === 'Enter') { this.go(this.sel >= 0 ? this.sel : 0, e.ctrlKey); e.preventDefault(); }
      else if (e.key === 'Escape') this.hide();
    });
    this.results.addEventListener('click', e => {
      const r = e.target.closest('.sr[data-i]');
      if (r) this.go(+r.dataset.i, e.ctrlKey || e.metaKey);
    });
  },

  show() {
    this.pane.hidden = false;
    $('splitH').hidden = false;
    this.input.focus();
    this.input.select();
    codeView.schedule();
  },

  hide() {
    this.pane.hidden = true;
    $('splitH').hidden = true;
    codeView.schedule();
  },

  invalidate() { this.addrIndex = null; if (!this.pane.hidden) this.run(); },

  schedule() { clearTimeout(this.timer); this.timer = setTimeout(() => this.run(), 120); },

  run() {
    const q = this.input.value.trim();
    const kind = this.kind.value;
    this.items = [];
    this.sel = -1;
    let total = 0;
    if (q) {
      const addr = parseAddress(q);
      if (kind === 'addr' || (kind === 'all' && addr !== null && /^0x/i.test(q))) {
        if (addr !== null) total = this.searchAddr(addr);
      } else {
        total = this.searchName(q, kind);
      }
    }
    this.renderResults(q, total);
  },

  searchName(q, kind) {
    const cs = $('searchCase').checked;
    const needle = cs ? q : q.toLowerCase();
    const dotted = needle.indexOf('.') >= 0;
    const norm = s => cs ? s : s.toLowerCase();
    const want = k => kind === 'all' ||
      (kind === 'method' && (k === 'method' || k === 'ctor')) ||
      (kind === 'field' && k === 'field') ||
      (kind === 'prop' && (k === 'property' || k === 'event')) ||
      (kind === 'const' && k === 'const');
    let total = 0;
    const exact = [], rest = [];
    const add = (item, nameStr) => {
      total++;
      const bucket = nameStr === needle ? exact : rest;
      if (exact.length + rest.length < MAX_RESULTS * 2) bucket.push(item);
    };
    for (const doc of docs.values()) {
      for (const t of doc.types) {
        if (kind === 'all' || kind === 'type') {
          const n = norm(t.simple);
          const full = dotted ? norm((t.ns ? t.ns + '.' : '') + t.key) : '';
          if (n.indexOf(needle) >= 0 || (dotted && full.indexOf(needle) >= 0)) add({ doc, t }, n);
        }
        if (kind === 'type') continue;
        const tk = dotted ? norm(t.key) + '.' : '';
        for (const m of t.members) {
          if (!want(m.kind)) continue;
          const n = norm(m.name);
          if (n.indexOf(needle) >= 0 || (dotted && (tk + n).indexOf(needle) >= 0)) add({ doc, t, m }, n);
        }
      }
    }
    this.items = exact.concat(rest).slice(0, MAX_RESULTS);
    return total;
  },

  buildAddrIndex() {
    const entries = [];
    for (const doc of docs.values()) {
      for (const t of doc.types) {
        for (const m of t.members) {
          if (m.rva >= 0) entries.push({ doc, t, m, a: m });
          if (m.gi) for (const g of m.gi) if (g.rva >= 0) entries.push({ doc, t, m, a: g, gi: g });
        }
      }
    }
    const sorted = field => entries.filter(e => e.a[field] >= 0).sort((x, y) => x.a[field] - y.a[field]);
    this.addrIndex = { rva: sorted('rva'), off: sorted('off'), va: sorted('va') };
  },

  searchAddr(addr) {
    if (!this.addrIndex) this.buildAddrIndex();
    const seen = new Set();
    const exact = [];
    const near = [];
    for (const field of ['rva', 'off', 'va']) {
      const arr = this.addrIndex[field];
      let lo = 0, hi = arr.length - 1, best = -1;
      while (lo <= hi) {
        const mid = (lo + hi) >> 1;
        if (arr[mid].a[field] <= addr) { best = mid; lo = mid + 1; } else hi = mid - 1;
      }
      if (best < 0) continue;
      const base = arr[best].a[field];
      let i = best;
      while (i > 0 && arr[i - 1].a[field] === base) i--;
      for (; i < arr.length && arr[i].a[field] === base; i++) {
        const e = arr[i];
        if (seen.has(e.a)) continue;
        seen.add(e.a);
        const item = Object.assign({ field, delta: addr - base }, e);
        (base === addr ? exact : near).push(item);
      }
    }
    // Если точного совпадения нет, показываем функцию, внутри которой лежит адрес.
    this.items = exact.length ? exact : near;
    return this.items.length;
  },

  renderResults(q, total) {
    if (!q) { this.results.innerHTML = ''; this.count.textContent = ''; return; }
    if (!docs.size) { this.results.innerHTML = '<div class="sr-note">Сначала откройте dump.cs</div>'; return; }
    if (!this.items.length) {
      this.results.innerHTML = '<div class="sr-note">Ничего не найдено</div>';
      this.count.textContent = '';
      return;
    }
    this.count.textContent = total > this.items.length ? `показано ${fmtInt(this.items.length)} из ${fmtInt(total)}` : `найдено: ${fmtInt(total)}`;
    const multi = docs.size > 1;
    let html = '<div class="sr head"><span>Имя</span><span>Тип</span><span>Сборка</span><span>RVA</span></div>';
    this.items.forEach((it, i) => {
      const { doc, t, m } = it;
      let name, owner, addr = '';
      if (!m) {
        name = `<span class="ic">${ICONS[t.kind]}</span>${typeLabel(t, true)}`;
        owner = `<span class="k-ns">${esc(t.ns || '-')}</span>`;
      } else {
        const label = it.gi ? `<span class="k-method">${esc(it.gi.name)}</span>` : memberLabel(m);
        name = `<span class="ic">${ICONS[m.kind]}</span><span class="lbl">${label}</span>`;
        owner = typeLabel(t, true);
        const a = it.a || m;
        if (a.rva >= 0) addr = hex(a.rva);
      }
      if (it.field && it.delta) addr = `${hex(it.a[it.field])} +${hex(it.delta)}`;
      const asm = esc(doc.images[t.image].name) + (multi ? ` <span class="dim">(${esc(doc.name)})</span>` : '');
      html += `<div class="sr" data-i="${i}"><span>${name}</span><span>${owner}</span><span>${asm}</span><span class="addr">${addr}</span></div>`;
    });
    if (this.items.length && this.items[0].field && this.items[0].delta) {
      html = `<div class="sr-note">Точного совпадения нет. Адрес попадает в ближайший предшествующий метод:</div>` + html;
    }
    this.results.innerHTML = html;
  },

  move(d) {
    if (!this.items.length) return;
    this.sel = Math.max(0, Math.min(this.items.length - 1, this.sel + d));
    this.results.querySelectorAll('.sr.sel').forEach(r => r.classList.remove('sel'));
    const r = this.results.querySelector(`.sr[data-i="${this.sel}"]`);
    if (r) { r.classList.add('sel'); r.scrollIntoView({ block: 'nearest' }); }
  },

  go(i, newTab) {
    const it = this.items[i];
    if (!it) return;
    this.sel = i;
    this.move(0);
    if (!it.m) openType(it.doc, it.t.id, -1, newTab, true);
    else openType(it.doc, it.t.id, it.m.idx, newTab, true, it.gi ? it.gi.line : undefined);
  },
};

function parseAddress(q) {
  const s = q.replace(/^0x/i, '').replace(/[`'_\s]/g, '');
  if (!/^[0-9a-f]+$/i.test(s) || s.length > 13) return null;
  return parseInt(s, 16);
}

// ---------------------------------------------------------------------------
// Разделители панелей
// ---------------------------------------------------------------------------

function makeSplitter(handle, onMove) {
  handle.addEventListener('pointerdown', e => {
    e.preventDefault();
    handle.setPointerCapture(e.pointerId);
    handle.classList.add('dragging');
    const move = ev => onMove(ev);
    const up = () => {
      handle.classList.remove('dragging');
      handle.removeEventListener('pointermove', move);
      handle.removeEventListener('pointerup', up);
    };
    handle.addEventListener('pointermove', move);
    handle.addEventListener('pointerup', up);
  });
}

function initSplitters() {
  const explorer = $('explorer');
  const savedW = +store('dnspyweb.treeWidth');
  if (savedW > 100) explorer.style.width = Math.min(savedW, window.innerWidth - 200) + 'px';
  makeSplitter($('splitV'), e => {
    const w = Math.max(160, Math.min(window.innerWidth - 200, e.clientX));
    explorer.style.width = w + 'px';
    store('dnspyweb.treeWidth', String(w));
  });
  const pane = $('searchPane');
  const savedH = +store('dnspyweb.searchHeight');
  if (savedH > 60) pane.style.height = savedH + 'px';
  makeSplitter($('splitH'), e => {
    const rect = $('right').getBoundingClientRect();
    const h = Math.max(80, Math.min(rect.height - 100, rect.bottom - e.clientY));
    pane.style.height = h + 'px';
    store('dnspyweb.searchHeight', String(h));
  });
}

// ---------------------------------------------------------------------------
// Запуск
// ---------------------------------------------------------------------------

function init() {
  tree.init();
  tabs.init();
  codeView.init();
  search.init();
  initSplitters();

  const input = $('fileInput');
  const pick = () => input.click();
  $('btnOpen').addEventListener('click', pick);
  $('welcomeOpen').addEventListener('click', e => { e.preventDefault(); pick(); });
  input.addEventListener('change', () => { const f = Array.from(input.files); input.value = ''; if (f.length) openFiles(f); });

  $('btnBack').addEventListener('click', () => tabs.go(-1));
  $('btnForward').addEventListener('click', () => tabs.go(1));
  $('btnSearch').addEventListener('click', () => search.pane.hidden ? search.show() : search.hide());
  $('optGeneric').addEventListener('change', () => { const t = tabs.current(); if (t) tabs.reload(t); });

  // Перетаскивание файла
  let dragDepth = 0;
  const hasFiles = e => e.dataTransfer && Array.from(e.dataTransfer.types).includes('Files');
  window.addEventListener('dragenter', e => { if (hasFiles(e)) { dragDepth++; $('drop').classList.add('on'); e.preventDefault(); } });
  window.addEventListener('dragleave', e => { if (hasFiles(e) && --dragDepth <= 0) { dragDepth = 0; $('drop').classList.remove('on'); } });
  window.addEventListener('dragover', e => { if (hasFiles(e)) e.preventDefault(); });
  window.addEventListener('drop', e => {
    if (!hasFiles(e)) return;
    e.preventDefault();
    dragDepth = 0;
    $('drop').classList.remove('on');
    const files = Array.from(e.dataTransfer.files);
    if (files.length) openFiles(files);
  });

  window.addEventListener('keydown', e => {
    const k = e.key.toLowerCase();
    if ((e.ctrlKey || e.metaKey) && e.shiftKey && k === 'k') { e.preventDefault(); search.show(); }
    else if ((e.ctrlKey || e.metaKey) && !e.shiftKey && k === 'o') { e.preventDefault(); pick(); }
    else if (e.altKey && e.key === 'ArrowLeft') { e.preventDefault(); tabs.go(-1); }
    else if (e.altKey && e.key === 'ArrowRight') { e.preventDefault(); tabs.go(1); }
  });
  window.addEventListener('mouseup', e => {
    if (e.button === 3) { e.preventDefault(); tabs.go(-1); }
    else if (e.button === 4) { e.preventDefault(); tabs.go(1); }
  });

  updateWelcome();
}

init();
