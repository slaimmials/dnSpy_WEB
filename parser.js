'use strict';

// Парсер дампов Il2CppDumper (dump.cs).
// Функция самодостаточная: app.js превращает её в исходник Web Worker'а через toString(),
// поэтому всё, что ей нужно, объявлено внутри неё.
function parseDump(text, onProgress) {
  if (text.charCodeAt(0) === 0xFEFF) text = text.slice(1);

  const len = text.length;
  let lineStarts = new Uint32Array(1 << 16);
  let lineCount = 0;

  const images = [];
  const types = [];

  let pendingNs = null;
  let pendingStart = -1;
  let cur = null;          // тип, внутри тела которого мы находимся
  let pendingAddr = null;  // последний комментарий "// RVA: ..." перед членом
  let lastMethod = null;
  let inGeneric = false;   // внутри блока /* GenericInstMethod : ... */
  let giAddr = null;

  // Разбивает строку по разделителю на верхнем уровне вложенности скобок.
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

  function splitWords(s) {
    return splitTop(s.trim(), ' ').filter(Boolean);
  }

  // "Dictionary<TKey, TValue>" -> "Dictionary"; "<Module>" и "<>c" не трогает.
  function stripGeneric(seg) {
    if (!seg.endsWith('>')) return seg;
    let depth = 0;
    for (let i = seg.length - 1; i >= 0; i--) {
      if (seg[i] === '>') depth++;
      else if (seg[i] === '<' && --depth === 0) return i > 0 ? seg.slice(0, i) : seg;
    }
    return seg;
  }

  function parseAddr(s) {
    const a = { rva: -1, off: -1, va: -1, slot: -1 };
    let m = /RVA: (0x[0-9A-Fa-f]+|-1)/.exec(s); if (m) a.rva = m[1] === '-1' ? -1 : parseInt(m[1], 16);
    m = /Offset: (0x[0-9A-Fa-f]+|-1)/.exec(s); if (m) a.off = m[1] === '-1' ? -1 : parseInt(m[1], 16);
    m = /VA: (0x[0-9A-Fa-f]+)/.exec(s); if (m) a.va = parseInt(m[1], 16);
    m = /Slot: (\d+)/.exec(s); if (m) a.slot = +m[1];
    return a;
  }

  function visOf(mods) {
    if (mods.includes('public')) return 'public';
    if (mods.includes('protected')) return mods.includes('internal') ? 'protected internal' : 'protected';
    if (mods.includes('internal')) return 'internal';
    return 'private';
  }

  function paramTypes(params) {
    if (!params.trim()) return [];
    return splitTop(params, ',').map(p => {
      p = p.trim().replace(/^(\[[^\]]*\]\s*)+/, '');
      const eq = p.indexOf(' = ');
      if (eq >= 0) p = p.slice(0, eq);
      const w = splitWords(p);
      if (w.length > 1) w.pop();
      return w.join(' ');
    });
  }

  function parseTypeDecl(decl, line) {
    const m = /^((?:[a-z]+ )*?)(class|struct|interface|enum) (.+)$/.exec(decl);
    if (!m) return null;
    const mods = m[1].trim().split(' ').filter(Boolean);
    let rest = m[3];
    let bases = [];
    const colon = rest.indexOf(' : ');
    if (colon >= 0) {
      bases = splitTop(rest.slice(colon + 3), ',').map(s => s.trim()).filter(Boolean);
      rest = rest.slice(0, colon);
    }
    const name = rest.trim();
    const segs = splitTop(name, '.');
    let kind = m[2];
    if (kind === 'class' && bases[0] === 'MulticastDelegate') kind = 'delegate';
    return {
      id: types.length,
      ns: pendingNs || '',
      name,                                         // как в дампе: "Outer.Inner<T>"
      short: segs[segs.length - 1],                 // "Inner<T>"
      key: segs.map(stripGeneric).join('.'),        // "Outer.Inner"
      simple: stripGeneric(segs[segs.length - 1]),  // "Inner"
      kind,
      mods,
      vis: visOf(mods),
      bases,
      index: -1,
      image: -1,
      parent: -1,
      start: pendingStart >= 0 ? pendingStart : line,
      decl: line,
      end: line,
      members: [],
    };
  }

  function parseMember(s, line) {
    const body = s.trim();
    const m = { kind: 'field', name: '', type: '', params: null, vis: 'private', isStatic: false,
                line, rva: -1, off: -1, va: -1, slot: -1, fieldOffset: -1, value: null, gi: null };
    const paren = body.indexOf('(');
    const eq = body.indexOf(' = ');
    const brace = body.indexOf(' { ');
    if (paren >= 0 && (eq < 0 || paren < eq) && (brace < 0 || paren < brace)) {
      // Метод: "mods ret name(params) { }" или "...;"
      const close = body.lastIndexOf(')');
      const head = splitWords(body.slice(0, paren));
      m.kind = 'method';
      m.name = head.pop() || '';
      m.type = head.pop() || 'void';
      m.mods = head;
      m.params = paramTypes(body.slice(paren + 1, close));
      if (m.name === '.ctor' || m.name === '.cctor') m.kind = 'ctor';
    } else if (brace >= 0 && /\{ (get|set|add|remove)\b/.test(body)) {
      const head = splitWords(body.slice(0, brace));
      m.name = head.pop() || '';
      m.type = head.pop() || '';
      m.mods = head;
      m.kind = head.includes('event') ? 'event' : 'property';
      m.accessors = body.slice(brace + 1).trim();
    } else {
      let decl = body;
      const cm = / \/\/ (0x[0-9A-Fa-f]+)$/.exec(decl);
      if (cm) { m.fieldOffset = parseInt(cm[1], 16); decl = decl.slice(0, cm.index); }
      if (decl.endsWith(';')) decl = decl.slice(0, -1);
      const e = decl.indexOf(' = ');
      if (e >= 0) { m.value = decl.slice(e + 3); decl = decl.slice(0, e); }
      const head = splitWords(decl);
      m.name = head.pop() || '';
      m.type = head.pop() || '';
      m.mods = head;
      if (head.includes('event')) m.kind = 'event';
      else if (head.includes('const')) m.kind = 'const';
    }
    m.vis = visOf(m.mods);
    m.isStatic = m.mods.includes('static') || m.mods.includes('const');
    return m;
  }

  let pos = 0;
  let nextReport = 0;
  while (pos <= len) {
    let nl = text.indexOf('\n', pos);
    if (nl < 0) nl = len;
    if (lineCount === lineStarts.length) {
      const grown = new Uint32Array(lineStarts.length * 2);
      grown.set(lineStarts);
      lineStarts = grown;
    }
    const ln = lineCount++;
    lineStarts[ln] = pos;
    let end = nl;
    if (end > pos && text.charCodeAt(end - 1) === 13) end--;
    const s = text.slice(pos, end);
    pos = nl + 1;

    if (onProgress && pos >= nextReport) {
      onProgress(pos / len);
      nextReport = pos + 1048576;
    }

    if (cur) {
      if (s === '}' || s === '{}') { cur.end = ln; cur = null; pendingAddr = null; lastMethod = null; inGeneric = false; continue; }
      if (s.charCodeAt(0) !== 9) continue;
      const t = s.trim();
      if (inGeneric) {
        if (t === '*/') { inGeneric = false; continue; }
        if (t.startsWith('|-RVA:')) giAddr = parseAddr(t);
        else if (t.startsWith('|-') && giAddr && lastMethod) {
          giAddr.name = t.slice(2);
          giAddr.line = ln;
          (lastMethod.gi || (lastMethod.gi = [])).push(giAddr);
          giAddr = null;
        }
        continue;
      }
      if (t === '') continue;
      if (t.startsWith('/* GenericInstMethod')) { inGeneric = true; giAddr = null; continue; }
      if (t.startsWith('//')) {
        if (t.startsWith('// RVA:')) pendingAddr = parseAddr(t);
        continue;
      }
      if (t[0] === '[' || t[0] === '/' || t[0] === '*' || t[0] === '|') continue;
      const mem = parseMember(s, ln);
      if (pendingAddr && (mem.kind === 'method' || mem.kind === 'ctor')) {
        mem.rva = pendingAddr.rva; mem.off = pendingAddr.off; mem.va = pendingAddr.va; mem.slot = pendingAddr.slot;
      }
      pendingAddr = null;
      if (mem.kind === 'method' || mem.kind === 'ctor') lastMethod = mem;
      cur.members.push(mem);
      continue;
    }

    if (s.startsWith('// Namespace:')) {
      pendingNs = s.slice(13).trim();
      pendingStart = ln;
      continue;
    }
    if (s.startsWith('// Image ')) {
      const m = /^\/\/ Image (\d+): (.+?) - (\d+)\s*$/.exec(s);
      if (m) images.push({ index: +m[1], name: m[2], first: +m[3] });
      continue;
    }
    const tdi = s.lastIndexOf('// TypeDefIndex:');
    if (tdi > 0 && s.charCodeAt(0) !== 9) {
      const t = parseTypeDecl(s.slice(0, tdi).trim(), ln);
      pendingNs = null;
      pendingStart = -1;
      if (!t) continue;
      t.index = parseInt(s.slice(tdi + 16), 10);
      types.push(t);
      if (s.endsWith('{}')) continue;
      // Тело начинается со строки "{" (или пустое "{}") на следующей строке.
      cur = t;
      t.end = ln;
      continue;
    }
  }

  // Привязка типов к сборкам по диапазонам TypeDefIndex.
  images.sort((a, b) => a.first - b.first);
  if (images.length) {
    let im = 0;
    const sorted = types.slice().sort((a, b) => a.index - b.index);
    for (const t of sorted) {
      while (im + 1 < images.length && images[im + 1].first <= t.index) im++;
      t.image = im;
    }
  } else {
    for (const t of types) t.image = 0;
  }

  // Вложенные типы: "Outer.Inner" -> родитель "Outer" в том же пространстве имён.
  // Il2CppDumper пишет у вложенных типов пустой "// Namespace:", поэтому ищем родителя
  // сначала в том же пространстве имён, затем по имени во всей сборке.
  const byKey = new Map(), byImageKey = new Map();
  for (const t of types) {
    const k = t.image + '|' + t.ns + '|' + t.key;
    if (!byKey.has(k)) byKey.set(k, t.id);
    const k2 = t.image + '|' + t.key;
    if (!byImageKey.has(k2) || types[byImageKey.get(k2)].key.indexOf('.') >= 0) byImageKey.set(k2, t.id);
  }
  const nestedOrder = types.filter(t => t.key.indexOf('.') > 0)
    .sort((a, b) => a.key.split('.').length - b.key.split('.').length);
  for (const t of nestedOrder) {
    const parentKey = t.key.slice(0, t.key.lastIndexOf('.'));
    let p = byKey.get(t.image + '|' + t.ns + '|' + parentKey);
    if (p === undefined) p = byImageKey.get(t.image + '|' + parentKey);
    if (p === undefined || p === t.id) continue;
    t.parent = p;
    t.ns = types[p].ns;
  }

  if (onProgress) onProgress(1);
  return { images, types, lineStarts: lineStarts.slice(0, lineCount), lineCount };
}

if (typeof module !== 'undefined') module.exports = { parseDump };
