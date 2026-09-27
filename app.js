/* LP-zoeker — offline zoeken in de LP-bibliotheek.
 * Alles draait lokaal op het toestel: de bibliotheek staat in IndexedDB,
 * de app zelf zit in de cache van de service worker. */
'use strict';

const APP_VERSIE = '1.2.0';
const MAX_TONEN = 40;
const THUMB_PX = 112;

/* ───────────────────────── IndexedDB ───────────────────────── */
const DB = (() => {
  let dbp = null;
  function open() {
    if (dbp) return dbp;
    dbp = new Promise((res, rej) => {
      const r = indexedDB.open('lpz', 1);
      r.onupgradeneeded = () => {
        const db = r.result;
        if (!db.objectStoreNames.contains('kv')) db.createObjectStore('kv');
        if (!db.objectStoreNames.contains('thumbs')) db.createObjectStore('thumbs');
      };
      r.onsuccess = () => res(r.result);
      r.onerror = () => rej(r.error);
    });
    return dbp;
  }
  async function tx(store, mode, fn) {
    const db = await open();
    return new Promise((res, rej) => {
      const t = db.transaction(store, mode);
      const s = t.objectStore(store);
      let out;
      Promise.resolve(fn(s)).then(v => { out = v; });
      t.oncomplete = () => res(out);
      t.onerror = () => rej(t.error);
      t.onabort = () => rej(t.error);
    });
  }
  const req = r => new Promise((res, rej) => { r.onsuccess = () => res(r.result); r.onerror = () => rej(r.error); });
  return {
    get: (k) => tx('kv', 'readonly', s => req(s.get(k))),
    set: (k, v) => tx('kv', 'readwrite', s => { s.put(v, k); }),
    thumbs: (keys) => tx('thumbs', 'readonly', s => Promise.all(keys.map(k => req(s.get(k))))),
    allThumbKeys: () => tx('thumbs', 'readonly', s => req(s.getAllKeys())),
    putThumbs: (entries, clear) => tx('thumbs', 'readwrite', s => {
      if (clear) s.clear();
      entries.forEach(([k, v]) => s.put(v, k));
    })
  };
})();

/* ───────────────────────── Tekst-normalisatie ───────────────────────── */
const SPECIAAL = { 'ø': 'o', 'æ': 'ae', 'œ': 'oe', 'ß': 'ss', 'ł': 'l', 'đ': 'd', 'þ': 'th', 'ı': 'i' };
function normChar(c) {
  const l = c.toLowerCase();
  if (SPECIAAL[l]) return SPECIAAL[l][0];
  const d = l.normalize('NFD').replace(/[̀-ͯ]/g, '');
  const ch = d[0] || ' ';
  return /[a-z0-9]/.test(ch) ? ch : ' ';
}
/** Genormaliseerde string met exact dezelfde lengte als het origineel (voor markeren). */
function normSameLen(s) { let o = ''; for (const c of String(s || '')) o += normChar(c); return o; }
function norm(s) {
  return String(s || '').toLowerCase()
    .replace(/[øæœßłđþı]/g, c => SPECIAAL[c])
    .normalize('NFD').replace(/[̀-ͯ]/g, '')
    .replace(/&/g, ' and ')
    .replace(/[^a-z0-9]+/g, ' ').trim();
}
const toks = s => { const n = norm(s); return n ? n.split(' ') : []; };

const STOP = new Set(('the a an of and in on at to for from with by or is it its my your our ' +
  'de het een en van in op te voor met la le les el los las der die das und du des ' +
  'vol volume lp ep stereo mono records record recordings music feat featuring ft ' +
  'original soundtrack side cd disc no nr op').split(' '));

/** Damerau-Levenshtein (beperkt), met vroegtijdig afbreken boven max. */
function dist(a, b, max) {
  const la = a.length, lb = b.length;
  if (Math.abs(la - lb) > max) return max + 1;
  let prev2 = null, prev = new Array(lb + 1), cur;
  for (let j = 0; j <= lb; j++) prev[j] = j;
  for (let i = 1; i <= la; i++) {
    cur = new Array(lb + 1); cur[0] = i; let rowMin = i;
    for (let j = 1; j <= lb; j++) {
      const cost = a[i - 1] === b[j - 1] ? 0 : 1;
      let v = Math.min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + cost);
      if (prev2 && i > 1 && j > 1 && a[i - 1] === b[j - 2] && a[i - 2] === b[j - 1]) v = Math.min(v, prev2[j - 2] + 1);
      cur[j] = v; if (v < rowMin) rowMin = v;
    }
    if (rowMin > max) return max + 1;
    prev2 = prev; prev = cur;
  }
  return prev[lb];
}

/* ───────────────────────── Bibliotheek in geheugen ───────────────────────── */
let LIB = [];          // items
let VOCAB = new Map(); // token -> [item-indexen] (artiest+album, zonder stopwoorden)
let IDF = new Map();
let GLUED = new Map(); // "pinkfloyd" -> [[i,'a'],…]
let META = null;       // { bijgewerkt, bron, aantal }

function bouwIndex() {
  VOCAB = new Map();
  LIB.forEach((it, i) => {
    it._na = norm(it.artiest); it._nb = norm(it.album);
    it._ta = it._na ? it._na.split(' ') : [];
    it._tb = it._nb ? it._nb.split(' ') : [];
    it._tx = toks([it.label, it.jaar, it.genre].join(' '));
    it._all = it._ta.concat(it._tb, it._tx);
    it._key = it._na + '|' + it._nb;
    const sig = new Set(it._ta.concat(it._tb).filter(t => t.length >= 2 && !STOP.has(t)));
    it._sig = [...sig];
    sig.forEach(t => { let a = VOCAB.get(t); if (!a) VOCAB.set(t, a = []); a.push(i); });
  });
  GLUED = new Map();
  LIB.forEach((it, i) => {
    [['a', it._ta], ['b', it._tb]].forEach(([deel, tt]) => {
      if (tt.length < 2) return;
      const g = tt.join('');
      if (g.length < 7) return;
      let l = GLUED.get(g); if (!l) GLUED.set(g, l = []); l.push([i, deel]);
    });
  });
  const N = LIB.length || 1;
  IDF = new Map();
  VOCAB.forEach((arr, t) => IDF.set(t, Math.log(1 + N / arr.length)));
  // Dubbels tellen
  const cnt = new Map();
  LIB.forEach(it => cnt.set(it._key, (cnt.get(it._key) || 0) + 1));
  LIB.forEach(it => { it._dup = cnt.get(it._key); });
}

/* ───────────────────────── Zoeken (typen) ───────────────────────── */
function zoek(q) {
  const qt = toks(q);
  if (!qt.length) return { exact: [], fuzzy: [] };
  const exact = [];
  for (let i = 0; i < LIB.length; i++) {
    const it = LIB[i];
    let score = 0, ok = true;
    for (const t of qt) {
      let best = 0;
      for (const w of it._ta) { if (w === t) best = Math.max(best, 5); else if (w.startsWith(t)) best = Math.max(best, 3.5); }
      for (const w of it._tb) { if (w === t) best = Math.max(best, 4.5); else if (w.startsWith(t)) best = Math.max(best, 3); }
      if (best < 3) for (const w of it._tx) { if (w.startsWith(t)) best = Math.max(best, 2); }
      if (!best && t.length >= 3 && (it._na.includes(t) || it._nb.includes(t))) best = 1;
      if (!best) { ok = false; break; }
      score += best;
    }
    if (ok) {
      const full = qt.join(' ');
      if (it._na === full || it._nb === full) score += 4;
      if (it._na.startsWith(full) || it._nb.startsWith(full)) score += 1.5;
      exact.push({ i, score });
    }
  }
  exact.sort((a, b) => b.score - a.score || cmpItem(LIB[a.i], LIB[b.i]));
  if (exact.length) return { exact, fuzzy: [] };

  // Niets exact → tolerant zoeken (tikfouten, andere schrijfwijze)
  const fuzzy = [];
  for (let i = 0; i < LIB.length; i++) {
    const it = LIB[i];
    let total = 0, ok = true;
    for (const t of qt) {
      const max = t.length >= 7 ? 2 : t.length >= 4 ? 1 : 0;
      let best = 99;
      for (const w of it._all) {
        if (w.startsWith(t)) { best = 0; break; }
        if (max) {
          best = Math.min(best, dist(t, w, max));
          if (w.length > t.length) best = Math.min(best, dist(t, w.slice(0, t.length), max));
        }
      }
      if (best > max) { ok = false; break; }
      total += best;
    }
    if (ok) fuzzy.push({ i, score: -total });
  }
  // Ook: woorden aan elkaar / los ("pinkfloyd", "abba gold" vs "abbagold")
  if (!fuzzy.length && qt.length) {
    const glued = qt.join('');
    if (glued.length >= 4) for (let i = 0; i < LIB.length; i++) {
      const it = LIB[i];
      const g = (it._na + it._nb).replace(/ /g, '');
      if (g.includes(glued)) fuzzy.push({ i, score: -1 });
    }
  }
  fuzzy.sort((a, b) => b.score - a.score || cmpItem(LIB[a.i], LIB[b.i]));
  return { exact: [], fuzzy };
}
function cmpItem(a, b) { return (a._na || '').localeCompare(b._na || '') || (a._nb || '').localeCompare(b._nb || ''); }

/* ───────────────────────── Hoes-vingerafdruk ───────────────────────── */
const FP_N = 32;
const _fpCanvas = document.createElement('canvas');
_fpCanvas.width = _fpCanvas.height = FP_N;
const _fpCtx = _fpCanvas.getContext('2d', { willReadFrequently: true });

/** src = image/canvas/video; rect = [sx,sy,sw,sh] (vierkant). Rand van 6% wordt genegeerd. */
function vingerafdruk(src, rect) {
  const [sx, sy, sw, sh] = rect;
  const inset = 0.06;
  _fpCtx.imageSmoothingEnabled = true;
  _fpCtx.imageSmoothingQuality = 'high';
  _fpCtx.clearRect(0, 0, FP_N, FP_N);
  _fpCtx.drawImage(src, sx + sw * inset, sy + sh * inset, sw * (1 - 2 * inset), sh * (1 - 2 * inset), 0, 0, FP_N, FP_N);
  const d = _fpCtx.getImageData(0, 0, FP_N, FP_N).data;
  const n = FP_N * FP_N;
  const R = new Float32Array(n), G = new Float32Array(n), B = new Float32Array(n), Y = new Float32Array(n);
  let sumY = 0;
  for (let p = 0, k = 0; p < n; p++, k += 4) {
    R[p] = d[k]; G[p] = d[k + 1]; B[p] = d[k + 2];
    Y[p] = 0.299 * d[k] + 0.587 * d[k + 1] + 0.114 * d[k + 2]; sumY += Y[p];
  }
  const M = sumY / n + 8;
  // 1) 4×4 kleurraster, helderheid-genormaliseerd
  const grid = [];
  const C = 4, cs = FP_N / C;
  for (let gy = 0; gy < C; gy++) for (let gx = 0; gx < C; gx++) {
    let r = 0, g = 0, b = 0, y = 0, c = 0;
    for (let yy = gy * cs; yy < (gy + 1) * cs; yy++) for (let xx = gx * cs; xx < (gx + 1) * cs; xx++) {
      const p = yy * FP_N + xx; r += R[p]; g += G[p]; b += B[p]; y += Y[p]; c++;
    }
    r /= c; g /= c; b /= c; y /= c;
    grid.push(+(y / M).toFixed(3), +((r - g) / (2 * M)).toFixed(3), +((r + g - 2 * b) / (4 * M)).toFixed(3));
  }
  // 2) gradiënt-hash (9×8 → 64 bits) op genormaliseerde helderheid
  const small = [];
  for (let yy = 0; yy < 8; yy++) for (let xx = 0; xx < 9; xx++) {
    let s = 0, c = 0;
    const x0 = Math.floor(xx * FP_N / 9), x1 = Math.floor((xx + 1) * FP_N / 9);
    const y0 = yy * 4, y1 = y0 + 4;
    for (let a = y0; a < y1; a++) for (let b2 = x0; b2 < Math.max(x1, x0 + 1); b2++) { s += Y[a * FP_N + b2]; c++; }
    small.push(s / c);
  }
  let h1 = 0, h2 = 0, bit = 0;
  for (let yy = 0; yy < 8; yy++) for (let xx = 0; xx < 8; xx++) {
    const v = small[yy * 9 + xx] > small[yy * 9 + xx + 1] ? 1 : 0;
    if (bit < 32) h1 = (h1 | (v << bit)) >>> 0; else h2 = (h2 | (v << (bit - 32))) >>> 0;
    bit++;
  }
  // 3) tint-histogram (12 tinten gewogen met verzadiging + 3 grijsniveaus)
  const hist = new Float32Array(15);
  for (let p = 0; p < n; p++) {
    const r = R[p] / 255, g = G[p] / 255, b = B[p] / 255;
    const mx = Math.max(r, g, b), mn = Math.min(r, g, b), dd = mx - mn;
    const s = mx ? dd / mx : 0;
    if (s < 0.18 || mx < 0.12) { hist[12 + Math.min(2, Math.floor((Y[p] / 255) * 3))] += 1; continue; }
    let h;
    if (mx === r) h = ((g - b) / dd) % 6; else if (mx === g) h = (b - r) / dd + 2; else h = (r - g) / dd + 4;
    h = (h * 60 + 360) % 360;
    hist[Math.floor(h / 30) % 12] += s;
  }
  let hs = 0; hist.forEach(v => { hs += v; });
  const histN = Array.from(hist, v => +(v / (hs || 1)).toFixed(3));
  return { g: grid, h: [h1, h2], c: histN };
}
function popcnt(x) { x -= (x >>> 1) & 0x55555555; x = (x & 0x33333333) + ((x >>> 2) & 0x33333333); return (((x + (x >>> 4)) & 0x0F0F0F0F) * 0x01010101) >>> 24; }
function fpAfstand(a, b) {
  let d1 = 0; for (let k = 0; k < a.g.length; k++) d1 += Math.abs(a.g[k] - b.g[k]);
  d1 /= a.g.length;
  const ham = popcnt(a.h[0] ^ b.h[0]) + popcnt(a.h[1] ^ b.h[1]);
  let d3 = 0; for (let k = 0; k < a.c.length; k++) d3 += Math.abs(a.c[k] - b.c[k]);
  d3 /= 2;
  return 0.5 * Math.min(1, d1 / 0.35) + 0.25 * (ham / 64) + 0.25 * d3;
}

/* ───────────────────────── Afbeeldingen ───────────────────────── */
function laadImg(src, ms = 15000) {
  return new Promise((res, rej) => {
    const im = new Image();
    if (/^https?:/i.test(src)) im.crossOrigin = 'anonymous';
    const t = setTimeout(() => { im.src = ''; rej(new Error('time-out')); }, ms);
    im.onload = () => { clearTimeout(t); res(im); };
    im.onerror = () => { clearTimeout(t); rej(new Error('img')); };
    im.src = src;
  });
}
/** Gratis beeld-proxy die CORS toestaat en verkleint — enkel gebruikt tijdens bijwerken,
 *  voor covers waarvan de oorspronkelijke site het kopiëren blokkeert. */
const proxyUrl = u => 'https://wsrv.nl/?url=' + encodeURIComponent(u.replace(/^https?:\/\//, '')) + '&w=300&h=300&fit=cover&output=jpg&q=80';
function vierkant(w, h, frac = 1) {
  const s = Math.min(w, h) * frac;
  return [(w - s) / 2, (h - s) / 2, s, s];
}
/** Maakt kleine thumbnail + vingerafdruk van een cover (data-URL of http-URL). */
async function verwerkCover(src) {
  if (!src) return { thumb: '', fp: null };
  src = src.trim();
  const pogingen = /^https?:/i.test(src) ? [src, proxyUrl(src)] : [src];
  for (const p of pogingen) {
    try {
      const im = await laadImg(p);
      const rect = vierkant(im.naturalWidth, im.naturalHeight);
      const cv = document.createElement('canvas');
      cv.width = cv.height = THUMB_PX;
      const cx = cv.getContext('2d');
      cx.imageSmoothingQuality = 'high';
      cx.drawImage(im, rect[0], rect[1], rect[2], rect[3], 0, 0, THUMB_PX, THUMB_PX);
      const thumb = cv.toDataURL('image/jpeg', 0.72); // gooit fout als de site kopiëren blokkeert
      return { thumb, fp: vingerafdruk(im, rect) };
    } catch (e) { /* volgende poging */ }
  }
  // Niet lokaal op te slaan: toon enkel online
  return { thumb: /^https?:/i.test(src) ? src : '', fp: null };
}
function hashStr(s) { let h = 2166136261; for (let i = 0; i < s.length; i += 7) { h ^= s.charCodeAt(i); h = Math.imul(h, 16777619); } return (h >>> 0).toString(36) + ':' + s.length; }

/* ───────────────────────── Synchroniseren ───────────────────────── */
function rijNaarItem(r, kol) {
  const o = {}; kol.forEach((k, i) => { o[k] = r[i] == null ? '' : String(r[i]); });
  return {
    id: o.id || '', artiest: o.artiest || '', album: o.album || '', jaar: o.jaar || '',
    label: o.label || '', genre: o.genre || '', notities: o.notities || '',
    kringwinkel: o.kringwinkel || '', bron: o.bron || '', _cover: o.cover || ''
  };
}

async function importeerItems(items, bronNaam, progress) {
  // Bestaande vingerafdrukken hergebruiken als de cover niet veranderde
  const oud = new Map();
  LIB.forEach((it, i) => { if (it.ch) oud.set(it.ch, { fp: it.fp, key: it.tk }); });
  const oudeThumbKeys = oud.size ? new Set(await DB.allThumbKeys()) : new Set();
  const oudeThumbs = new Map();
  const nodig = [];
  items.forEach((it, i) => {
    it.tk = 't' + i;
    it.ch = it._cover ? hashStr(it._cover) : '';
    const o = it.ch && oud.get(it.ch);
    if (o && o.fp && o.key && oudeThumbKeys.has(o.key)) { it.fp = o.fp; it._reuse = o.key; }
    else if (it._cover) nodig.push(it);
  });
  // Oude thumbs die we hergebruiken ophalen
  const reuse = items.filter(it => it._reuse);
  for (let k = 0; k < reuse.length; k += 200) {
    const part = reuse.slice(k, k + 200);
    const vals = await DB.thumbs(part.map(it => it._reuse));
    part.forEach((it, j) => oudeThumbs.set(it.tk, vals[j] || ''));
  }
  const nieuweThumbs = new Map();
  let klaar = 0;
  const PAR = 4;
  for (let k = 0; k < nodig.length; k += PAR) {
    await Promise.all(nodig.slice(k, k + PAR).map(async it => {
      const r = await verwerkCover(it._cover);
      it.fp = r.fp; nieuweThumbs.set(it.tk, r.thumb);
    }));
    klaar += Math.min(PAR, nodig.length - k);
    progress && progress(klaar / nodig.length, `Hoezen verwerken ${klaar}/${nodig.length}`);
  }
  const entries = [];
  items.forEach(it => {
    const t = nieuweThumbs.has(it.tk) ? nieuweThumbs.get(it.tk) : oudeThumbs.get(it.tk);
    it.heeftThumb = !!t;
    if (t) entries.push([it.tk, t]);
    delete it._cover; delete it._reuse;
  });
  await DB.putThumbs(entries, true);
  THUMBS.clear();
  const meta = { bijgewerkt: new Date().toISOString(), bron: bronNaam, aantal: items.length, versie: APP_VERSIE };
  await DB.set('lib', items);
  await DB.set('meta', meta);
  LIB = items; META = meta;
  bouwIndex();
}

async function syncVanUrl(stil) {
  const url = (await DB.get('url')) || '';
  if (!url) { if (!stil) toast('Stel eerst de export-link in (⚙︎).'); return false; }
  if (!navigator.onLine) { if (!stil) toast('Geen internet — je werkt verder met de bewaarde bibliotheek.'); return false; }
  setProg(0.02, 'Bibliotheek ophalen…');
  try {
    const ctrl = new AbortController();
    const to = setTimeout(() => ctrl.abort(), 60000);
    const resp = await fetch(url, { signal: ctrl.signal, cache: 'no-store' });
    clearTimeout(to);
    if (!resp.ok) throw new Error('HTTP ' + resp.status);
    const items = parseTekst(await resp.text());
    if (!items.length) throw new Error('Geen LP\'s ontvangen');
    setProg(0.05, `${items.length} LP's ontvangen, hoezen verwerken…`);
    await importeerItems(items, 'Google Sheet', setProg);
    setProg(null);
    if (!stil) toast(`✓ ${items.length} LP's bijgewerkt`);
    render();
    return true;
  } catch (e) {
    setProg(null);
    if (!stil) toast('Bijwerken mislukt: ' + (e.name === 'AbortError' ? 'time-out' : e.message) + '. Je bewaarde bibliotheek blijft bruikbaar.');
    return false;
  } finally { toonStatus(); }
}

/* CSV/JSON import (reserve, als de export-link niet gebruikt wordt) */
function parseCSV(txt) {
  const rows = []; let row = [], f = '', q = false;
  for (let i = 0; i < txt.length; i++) {
    const c = txt[i];
    if (q) {
      if (c === '"') { if (txt[i + 1] === '"') { f += '"'; i++; } else q = false; }
      else f += c;
    } else if (c === '"') q = true;
    else if (c === ',') { row.push(f); f = ''; }
    else if (c === '\n' || c === '\r') { if (c === '\r' && txt[i + 1] === '\n') i++; row.push(f); rows.push(row); row = []; f = ''; }
    else f += c;
  }
  if (f || row.length) { row.push(f); rows.push(row); }
  return rows;
}
/** Leest JSON (Apps Script-export) of CSV (gepubliceerde sheet / download) naar items. */
function parseTekst(txt) {
  txt = txt.replace(/^\uFEFF/, '');
  if (/^\s*[\[{]/.test(txt)) {
    const data = JSON.parse(txt);
    if (data.ok === false) throw new Error(data.fout || 'Export gaf een fout');
    return data.rijen ? data.rijen.map(r => rijNaarItem(r, data.kolommen)) : [];
  }
  if (/^\s*<(!doctype|html)/i.test(txt)) throw new Error('De link gaf een webpagina terug i.p.v. gegevens (is de sheet gepubliceerd als CSV?)');
  const rows = parseCSV(txt);
  const kop = rows[0].map(h => h.trim().toLowerCase());
  const map = { id: 'id', artiest: 'artiest', album: 'album', jaar: 'jaar', label: 'label', genre: 'genre',
    notities: 'notities', opmerkingenkringwinkel: 'kringwinkel', coverurl: 'cover', bronurl: 'bron' };
  const kol = kop.map(h => map[h] || ('_' + h));
  if (kol.indexOf('artiest') < 0 || kol.indexOf('album') < 0) throw new Error('Kolommen "Artiest" en "Album" niet gevonden (juiste tabblad gepubliceerd?)');
  return rows.slice(1).map(r => rijNaarItem(r, kol)).filter(it => it.artiest || it.album);
}
async function importeerBestand(file) {
  const items = parseTekst(await file.text());
  if (!items.length) throw new Error('Geen LP\'s gevonden in het bestand');
  setProg(0.05, `${items.length} LP's gelezen, hoezen verwerken…`);
  await importeerItems(items, 'Bestand: ' + file.name, setProg);
  setProg(null);
  toast(`✓ ${items.length} LP's geïmporteerd`);
  render(); toonStatus();
}

/* ───────────────────────── Tekstherkenning (OCR) ───────────────────────── */
const OCR_DIR = 'vendor/ocr/';
let ocrWorkerP = null;
function simdOK() {
  try {
    return WebAssembly.validate(new Uint8Array([0, 97, 115, 109, 1, 0, 0, 0, 1, 5, 1, 96, 0, 1, 123, 3, 2, 1, 0, 10, 10, 1, 8, 0, 65, 0, 253, 15, 253, 98, 11]));
  } catch (e) { return false; }
}
function ocrBestanden() {
  return ['tesseract.min.js', 'worker.min.js', simdOK() ? 'tesseract-core-simd-lstm.wasm.js' : 'tesseract-core-lstm.wasm.js', 'eng.traineddata.gz'];
}
function laadScript(src) {
  return new Promise((res, rej) => {
    const s = document.createElement('script'); s.src = src; s.onload = res; s.onerror = () => rej(new Error('script ' + src));
    document.head.appendChild(s);
  });
}
async function blobUrl(naam, type) {
  const r = await fetch(OCR_DIR + naam);
  if (!r.ok) throw new Error(naam + ' niet beschikbaar');
  return URL.createObjectURL(new Blob([await r.arrayBuffer()], { type }));
}
/** Alle OCR-bestanden worden in de hoofdpagina opgehaald (via de offline-cache) en als
 *  blob-URL aan de worker gegeven — zo werkt het ook zonder internet. */
function ocrWorker() {
  if (ocrWorkerP) return ocrWorkerP;
  ocrWorkerP = (async () => {
    const [lib, wrk, core, lang] = ocrBestanden();
    if (!window.Tesseract) await laadScript(OCR_DIR + lib);
    const wUrl = await blobUrl(wrk, 'application/javascript');
    const cUrl = await blobUrl(core, 'application/javascript');
    const lUrl = await blobUrl(lang, 'application/gzip');
    const wrapper = `const __f=self.fetch.bind(self);self.fetch=function(u,o){return __f(String(u).indexOf('traineddata')>-1?${JSON.stringify(lUrl)}:u,o)};importScripts(${JSON.stringify(wUrl)});`;
    const wrapUrl = URL.createObjectURL(new Blob([wrapper], { type: 'application/javascript' }));
    const w = await Tesseract.createWorker('eng', 1, {
      workerPath: wrapUrl, workerBlobURL: false,
      corePath: cUrl + '#core.wasm.js',
      langPath: 'https://offline.local/ocr', cacheMethod: 'none', gzip: true
    });
    await w.setParameters({ tessedit_pageseg_mode: '11' });
    return w;
  })();
  ocrWorkerP.catch(() => { ocrWorkerP = null; });
  return ocrWorkerP;
}
async function ocrKlaarzetten(knop) {
  const st = document.getElementById('ocrStat');
  try {
    knop && (knop.disabled = true);
    st.textContent = 'Bezig met laden…';
    for (const f of ocrBestanden()) { const r = await fetch(OCR_DIR + f); if (!r.ok) throw new Error(f); await r.blob(); }
    await ocrWorker();
    st.textContent = '✓ Tekstherkenning staat klaar en werkt offline.';
    await DB.set('ocrKlaar', true);
  } catch (e) {
    st.textContent = 'Laden mislukt (' + e.message + '). Probeer opnieuw met internet.';
  } finally { knop && (knop.disabled = false); }
}

function ocrMatch(tekst) {
  const woorden = [...new Set(toks(tekst).filter(t => t.length >= 3 && /[a-z]/.test(t)))];
  const perItem = new Map(); // i -> Map(itemToken -> 1)
  const herkend = new Map(); // ocr-woord -> vocab-woord
  const vocabKeys = [...VOCAB.keys()];
  for (const w of woorden) {
    const hits = [];
    if (VOCAB.has(w) && !STOP.has(w)) hits.push(w);
    else if (w.length >= 5) {
      const max = w.length >= 8 ? 2 : 1;
      for (const v of vocabKeys) {
        if (Math.abs(v.length - w.length) > max || v.length < 4) continue;
        if (v[0] !== w[0] && v[1] !== w[1]) continue;
        if (dist(w, v, max) <= max) hits.push(v);
      }
    }
    hits.forEach(v => {
      herkend.set(w, v);
      VOCAB.get(v).forEach(i => { let m = perItem.get(i); if (!m) perItem.set(i, m = new Set()); m.add(v); });
    });
    // Aan elkaar geplakte woorden ("PINKFLOYD", "JACQUESBREL")
    if (!hits.length && w.length >= 7) {
      GLUED.forEach((lijst, g) => {
        const max = g.length >= 10 ? 2 : 1;
        if (!(w.includes(g) || (g.includes(w) && w.length >= 8) || (Math.abs(g.length - w.length) <= max && dist(w, g, max) <= max))) return;
        lijst.forEach(([i, deel]) => {
          const it = LIB[i];
          const tt = (deel === 'a' ? it._ta : it._tb).filter(t => VOCAB.has(t));
          let m = perItem.get(i); if (!m) perItem.set(i, m = new Set());
          tt.forEach(t => { m.add(t); herkend.set(w + t, t); });
        });
      });
    }
  }
  const res = [];
  perItem.forEach((set, i) => {
    const it = LIB[i];
    let tot = 0; it._sig.forEach(t => { tot += IDF.get(t) || 0; });
    let got = 0, lang = false; set.forEach(t => { got += IDF.get(t) || 0; if (t.length >= 4) lang = true; });
    if (!lang && set.size < 2) return;
    const cov = tot ? got / tot : 0;
    const sterk = Math.min(1, got / 7) * (0.35 + 0.65 * cov);
    const heeftArt = it._ta.some(t => set.has(t)), heeftAlb = it._tb.some(t => set.has(t));
    res.push({ i, sterk: sterk + (heeftArt && heeftAlb ? 0.25 : 0), cov, woorden: [...set], alb: heeftAlb, art: heeftArt });
  });
  res.sort((a, b) => b.sterk - a.sterk);
  return { res, herkend: [...new Set(herkend.values())] };
}

/** Lokale (adaptieve) drempel: maakt tekst zwart-op-wit, ook op kleurrijke hoezen.
 *  inv=true zoekt lichte tekst op donkere ondergrond. */
function binariseer(src, S, inv) {
  const cv = document.createElement('canvas');
  cv.width = cv.height = S;
  const cx = cv.getContext('2d', { willReadFrequently: true });
  cx.drawImage(src, 0, 0, S, S);
  const d = cx.getImageData(0, 0, S, S), a = d.data;
  const Y = new Float32Array(S * S);
  for (let p = 0, k = 0; p < S * S; p++, k += 4) Y[p] = 0.299 * a[k] + 0.587 * a[k + 1] + 0.114 * a[k + 2];
  const W = S + 1, I = new Float64Array(W * W);
  for (let y = 0; y < S; y++) { let row = 0; for (let x = 0; x < S; x++) { row += Y[y * S + x]; I[(y + 1) * W + x + 1] = I[y * W + x + 1] + row; } }
  const R = Math.round(S / 40), C = 12;
  for (let y = 0; y < S; y++) {
    const y0 = Math.max(0, y - R), y1 = Math.min(S, y + R + 1);
    for (let x = 0; x < S; x++) {
      const x0 = Math.max(0, x - R), x1 = Math.min(S, x + R + 1);
      const m = (I[y1 * W + x1] - I[y0 * W + x1] - I[y1 * W + x0] + I[y0 * W + x0]) / ((x1 - x0) * (y1 - y0));
      const v = Y[y * S + x];
      const inkt = inv ? v > m + C : v < m - C;
      const k = (y * S + x) * 4;
      a[k] = a[k + 1] = a[k + 2] = inkt ? 0 : 255;
    }
  }
  cx.putImageData(d, 0, 0);
  return cv;
}

function hoesMatch(fp) {
  const d = [];
  for (let i = 0; i < LIB.length; i++) if (LIB[i].fp) d.push({ i, d: fpAfstand(fp, LIB[i].fp) });
  if (d.length < 3) return [];
  let m = 0; d.forEach(x => { m += x.d; }); m /= d.length;
  let v = 0; d.forEach(x => { v += (x.d - m) ** 2; }); const sd = Math.sqrt(v / d.length) || 1;
  d.forEach(x => { x.z = (m - x.d) / sd; });
  d.sort((a, b) => a.d - b.d);
  return d.slice(0, 12);
}

async function verwerkFoto(src, rect) {
  toonBusy('Hoes vergelijken…');
  try {
    // Uitsnede op vaste grootte
    const cv = document.createElement('canvas');
    const S = 1100;
    cv.width = cv.height = S;
    const cx = cv.getContext('2d');
    cx.drawImage(src, rect[0], rect[1], rect[2], rect[3], 0, 0, S, S);
    const shot = cv.toDataURL('image/jpeg', 0.6);
    const fp = vingerafdruk(cv, [0, 0, S, S]);
    const hoes = hoesMatch(fp);
    let ocr = { res: [], herkend: [] }, ocrFout = '';
    try {
      toonBusy('Tekst lezen…');
      const w = await ocrWorker();
      // Twee doorgangen: donkere tekst op lichte achtergrond, en omgekeerd
      const t1 = (await w.recognize(binariseer(cv, 900, false))).data.text || '';
      const t2 = (await w.recognize(binariseer(cv, 900, true))).data.text || '';
      const tekst = t1 + '\n' + t2;
      ocr = ocrMatch(tekst);
      ocr.ruw = tekst.replace(/\s+/g, ' ').trim();
    } catch (e) { ocrFout = 'Tekstherkenning niet beschikbaar (eerst één keer met internet openen).'; }
    // Combineren
    const cand = new Map();
    ocr.res.slice(0, 15).forEach(r => cand.set(r.i, { i: r.i, t: r.sterk, h: 0, w: r.woorden, art: r.art, alb: r.alb }));
    hoes.forEach(h => {
      const hp = Math.max(0, Math.min(1, (h.z - 2) / 3.5));
      const c = cand.get(h.i) || { i: h.i, t: 0, h: 0, w: [] };
      c.h = hp; c.z = h.z; cand.set(h.i, c);
    });
    const lijst = [...cand.values()].map(c => ({ ...c, s: c.t + 0.8 * c.h + (c.t > 0.3 && c.h > 0.2 ? 0.3 : 0) }))
      .filter(c => c.s > 0.12).sort((a, b) => b.s - a.s)
      .filter((c, k, arr) => arr.findIndex(x => LIB[x.i]._key === LIB[c.i]._key) === k) // dubbels 1×
      .slice(0, 10);
    FOTO = { shot, lijst, ocr, ocrFout };
    document.getElementById('q').value = '';
    render();
  } finally { verbergBusy(); }
}

/* ───────────────────────── Camera ───────────────────────── */
let stream = null;
async function openCamera() {
  if (!LIB.length) { toast('Nog geen bibliotheek geladen (⚙︎).'); return; }
  if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia) { document.getElementById('fileCam').click(); return; }
  const cv = document.getElementById('camview');
  const video = document.getElementById('video');
  try {
    stream = await navigator.mediaDevices.getUserMedia({
      video: { facingMode: { ideal: 'environment' }, width: { ideal: 1920 }, height: { ideal: 1080 } }, audio: false
    });
    video.srcObject = stream;
    cv.classList.add('open');
    await video.play().catch(() => {});
    ocrWorker().catch(() => {}); // alvast opwarmen
  } catch (e) {
    stopCamera();
    document.getElementById('fileCam').click();
  }
}
function stopCamera() {
  if (stream) stream.getTracks().forEach(t => t.stop());
  stream = null;
  document.getElementById('camview').classList.remove('open');
}
function neemFoto() {
  const video = document.getElementById('video');
  const vw = video.videoWidth, vh = video.videoHeight;
  if (!vw) return;
  const W = video.clientWidth, H = video.clientHeight;
  const sc = Math.max(W / vw, H / vh);
  const ox = (W - vw * sc) / 2, oy = (H - vh * sc) / 2;
  const g = document.querySelector('.guide').getBoundingClientRect();
  const vr = video.getBoundingClientRect();
  let sx = (g.left - vr.left - ox) / sc, sy = (g.top - vr.top - oy) / sc, s = g.width / sc;
  s = Math.min(s, vw, vh); sx = Math.max(0, Math.min(vw - s, sx)); sy = Math.max(0, Math.min(vh - s, sy));
  const snap = document.createElement('canvas');
  snap.width = vw; snap.height = vh;
  snap.getContext('2d').drawImage(video, 0, 0, vw, vh);
  stopCamera();
  verwerkFoto(snap, [sx, sy, s, s]);
}
async function fotoUitBestand(file) {
  if (!file) return;
  try {
    const url = URL.createObjectURL(file);
    const im = await laadImg(url);
    await verwerkFoto(im, vierkant(im.naturalWidth, im.naturalHeight, 0.92));
    URL.revokeObjectURL(url);
  } catch (e) { toast('Foto kon niet gelezen worden.'); }
}

/* ───────────────────────── Weergave ───────────────────────── */
let FOTO = null;
let KW_MODUS = false;
let toonAlles = false;
const THUMBS = new Map();
const esc = s => String(s || '').replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));

function markeer(orig, qt) {
  if (!qt || !qt.length || !orig) return esc(orig);
  const n = normSameLen(orig);
  const mark = new Array(orig.length).fill(false);
  const chars = [...orig];
  const nn = [...n];
  const nstr = nn.join('');
  qt.forEach(t => {
    let from = 0, idx;
    while ((idx = nstr.indexOf(t, from)) > -1) {
      if (idx === 0 || nstr[idx - 1] === ' ') for (let k = idx; k < idx + t.length; k++) mark[k] = true;
      from = idx + 1;
    }
  });
  let out = '', open = false;
  chars.forEach((c, k) => {
    if (mark[k] && !open) { out += '<mark>'; open = true; }
    if (!mark[k] && open) { out += '</mark>'; open = false; }
    out += esc(c);
  });
  if (open) out += '</mark>';
  return out;
}

function kaart(it, qt, extra) {
  const meta = [it.jaar, it.label, it.genre].filter(Boolean).map(esc).join(' · ');
  return `<div class="card">
    <img data-tk="${esc(it.heeftThumb ? it.tk : '')}" alt="" style="${it.heeftThumb ? '' : 'display:none'}">
    ${it.heeftThumb ? '' : '<div class="ph">💿</div>'}
    <div class="body">
      <div class="art">${markeer(it.artiest || '(onbekende artiest)', qt)}${it._dup > 1 ? `<span class="pill dup">${it._dup}×</span>` : ''}${extra || ''}</div>
      <div class="alb">${markeer(it.album || '', qt)}</div>
      ${meta ? `<div class="meta">${meta}</div>` : ''}
      ${it.kringwinkel ? `<div class="note kw">🏪 ${esc(it.kringwinkel)}</div>` : ''}
      ${it.notities && !/^Toegevoegd via/i.test(it.notities) ? `<div class="note">📝 ${esc(it.notities)}</div>` : ''}
    </div>
  </div>`;
}

async function vulThumbs() {
  const imgs = [...document.querySelectorAll('img[data-tk]')].filter(im => im.dataset.tk);
  const nodig = [...new Set(imgs.map(im => im.dataset.tk).filter(k => !THUMBS.has(k)))];
  if (nodig.length) {
    const vals = await DB.thumbs(nodig);
    nodig.forEach((k, j) => THUMBS.set(k, vals[j] || ''));
  }
  imgs.forEach(im => { const v = THUMBS.get(im.dataset.tk); if (v) im.src = v; });
}

function render() {
  const out = document.getElementById('out');
  const q = document.getElementById('q').value;
  document.getElementById('clear').style.display = q ? 'block' : 'none';
  if (!LIB.length) {
    out.innerHTML = `<div class="empty"><div class="big">💿</div>Nog geen bibliotheek op dit toestel.<br><br>
      Tik op <b>⚙︎</b> om de export-link in te stellen en de bibliotheek op te halen (één keer met internet).</div>`;
    return;
  }
  zetKwKnop();
  if (KW_MODUS) return renderKw(out, q);
  if (FOTO && !q.trim()) return renderFoto(out);
  FOTO = null;
  const qt = toks(q);
  if (!qt.length) {
    const d = META && META.bijgewerkt ? new Date(META.bijgewerkt) : null;
    out.innerHTML = `<div class="empty"><div class="big">🔎</div>
      <b>${LIB.length}</b> LP's offline beschikbaar${d ? `<br><small>bijgewerkt ${d.toLocaleDateString('nl-BE')} ${d.toLocaleTimeString('nl-BE', { hour: '2-digit', minute: '2-digit' })}</small>` : ''}
      <br><br>Typ een naam, of neem een foto van de hoes met 📷.
      <br><br><small>Tip: houd het zoekveld ingedrukt → <b>Scan tekst</b> om tekst van de hoes in te lezen met de iPhone-camera.</small></div>`;
    return;
  }
  const { exact, fuzzy } = zoek(q);
  let html = '';
  const gezien = new Set();
  const lijst = (exact.length ? exact : fuzzy).filter(r => { const k = LIB[r.i]._key; if (gezien.has(k)) return false; gezien.add(k); return true; });
  const aantalEx = exact.reduce((n, r) => n + 1, 0);
  const uniek = lijst.length;
  const metKw = lijst.filter(r => LIB[r.i].kringwinkel).length;
  if (exact.length && metKw && metKw === lijst.length) {
    html += `<div class="verdict v-kw"><span class="big">🏪</span><div>Hebben we al — maar met een gebrek<small>${lijst.length === 1 ? 'Deze LP staat' : 'Deze LP\'s staan'} op de lijst “te vervangen”: opnieuw kopen kan interessant zijn</small></div></div>`;
  } else if (exact.length) {
    html += `<div class="verdict v-ok"><span class="big">✓</span><div>Hebben we al${uniek > 1 ? ` — ${uniek} titels` : ''}<small>${aantalEx} exempla${aantalEx === 1 ? 'ar' : 'ren'} gevonden voor “${esc(q.trim())}”${metKw ? ` · ${metKw} met kringwinkel-opmerking` : ''}</small></div></div>`;
  } else if (fuzzy.length) {
    html += `<div class="verdict v-maybe"><span class="big">?</span><div>Niet exact gevonden<small>Maar dit lijkt erop — controleer de spelling</small></div></div>`;
  } else {
    html += `<div class="verdict v-no"><span class="big">✗</span><div>Niet in de collectie<small>Niets gevonden voor “${esc(q.trim())}”, ook niet met tikfouten</small></div></div>`;
  }
  const n = toonAlles ? lijst.length : Math.min(MAX_TONEN, lijst.length);
  html += lijst.slice(0, n).map(r => kaart(LIB[r.i], qt, fuzzy.length ? '<span class="pill sim">lijkt op</span>' : '')).join('');
  if (lijst.length > n) html += `<button class="more" id="meer">Toon alle ${lijst.length}</button>`;
  out.innerHTML = html;
  const m = document.getElementById('meer'); if (m) m.onclick = () => { toonAlles = true; render(); };
  vulThumbs();
}

function zetKwKnop() {
  const b = document.getElementById('btnKw');
  const n = new Set(LIB.filter(it => it.kringwinkel).map(it => it._key)).size;
  b.style.display = n ? '' : 'none';
  b.classList.toggle('on', KW_MODUS);
  b.innerHTML = KW_MODUS ? `🏪 Te vervangen (${n}) <b>✕</b>` : `🏪 Te vervangen <span>${n}</span>`;
  document.getElementById('q').placeholder = KW_MODUS ? 'Filter in de lijst…' : 'Artiest of album…';
}

function renderKw(out, q) {
  const qt = toks(q);
  let idx = LIB.map((it, i) => i).filter(i => LIB[i].kringwinkel);
  if (qt.length) {
    const hit = new Set(zoek(q).exact.map(r => r.i));
    idx = idx.filter(i => hit.has(i) || norm(LIB[i].kringwinkel).includes(qt.join(' ')));
  }
  const gezien = new Set();
  idx = idx.filter(i => { const k = LIB[i]._key; if (gezien.has(k)) return false; gezien.add(k); return true; })
    .sort((a, b) => cmpItem(LIB[a], LIB[b]));
  let html = `<div class="verdict v-kw"><span class="big">🏪</span><div>Te vervangen: ${idx.length} LP${idx.length === 1 ? '' : '\'s'}${qt.length ? ' (gefilterd)' : ''}<small>LP's met een kringwinkel-opmerking (bv. hoes beschadigd). Zie je er één? Dan kan kopen de moeite zijn.</small></div></div>`;
  if (!idx.length) html += `<div class="empty">Niets gevonden in deze lijst.</div>`;
  html += idx.map(i => kaart(LIB[i], qt)).join('');
  out.innerHTML = html;
  vulThumbs();
}

function renderFoto(out) {
  const { shot, lijst, ocr, ocrFout } = FOTO;
  let html = '';
  const top = lijst[0];
  if (top && top.s >= 0.85) html += `<div class="verdict v-ok"><span class="big">✓</span><div>Waarschijnlijk hebben we deze al<small>Controleer hieronder of het dezelfde persing is</small></div></div>`;
  else if (top && top.s >= 0.35 && top.art && !top.alb && top.h < 0.3) html += `<div class="verdict v-maybe"><span class="big">?</span><div>Artiest zit in de collectie<small>Maar dit album misschien niet — vergelijk de titels hieronder</small></div></div>`;
  else if (top && top.s >= 0.35) html += `<div class="verdict v-maybe"><span class="big">?</span><div>Mogelijk in de collectie<small>Niet zeker — vergelijk de suggesties of typ de naam</small></div></div>`;
  else html += `<div class="verdict v-no"><span class="big">✗</span><div>Niets herkend<small>Waarschijnlijk niet in de collectie — typ de naam om zeker te zijn</small></div></div>`;
  html += `<img class="shot" src="${shot}" alt="">`;
  if (ocr.herkend.length) {
    html += `<div class="sect">Herkende woorden — tik om te zoeken</div><div class="chips">` +
      ocr.herkend.slice(0, 14).map(w => `<button class="chip hit" data-w="${esc(w)}">${esc(w)}</button>`).join('') + `</div>`;
  } else if (ocrFout) {
    html += `<div class="sect">Tekst</div><div class="meta" style="color:var(--dim);font-size:13.5px">${esc(ocrFout)}</div>`;
  } else {
    html += `<div class="sect">Tekst</div><div class="meta" style="color:var(--dim);font-size:13.5px">Geen bruikbare tekst op de hoes gelezen.</div>`;
  }
  html += `<div style="clear:both"></div>`;
  if (lijst.length) {
    html += `<div class="sect">Beste overeenkomsten</div>`;
    html += lijst.map(c => {
      const tags = (c.t > 0.2 ? '<span class="pill sim">tekst</span>' : '') + (c.h > 0.15 ? '<span class="pill sim">hoes</span>' : '');
      return kaart(LIB[c.i], c.w || [], tags);
    }).join('');
  }
  html += `<button class="more" id="fotoWeg">Nieuwe zoekopdracht</button>`;
  out.innerHTML = html;
  out.querySelectorAll('.chip').forEach(b => b.onclick = () => {
    const q = document.getElementById('q');
    q.value = (q.value ? q.value + ' ' : '') + b.dataset.w; FOTO = null; render();
  });
  document.getElementById('fotoWeg').onclick = () => { FOTO = null; render(); document.getElementById('q').focus(); };
  vulThumbs();
}

/* ───────────────────────── UI-hulp ───────────────────────── */
let toastT;
function toast(msg) { const t = document.getElementById('toast'); t.textContent = msg; t.classList.add('open'); clearTimeout(toastT); toastT = setTimeout(() => t.classList.remove('open'), 4200); }
function toonBusy(t) { document.getElementById('busyTxt').textContent = t; document.getElementById('busy').classList.add('open'); }
function verbergBusy() { document.getElementById('busy').classList.remove('open'); }
function setProg(frac, txt) {
  const p = document.getElementById('prog');
  if (frac == null) { p.style.display = 'none'; return; }
  p.style.display = 'block'; p.firstElementChild.style.width = Math.round(frac * 100) + '%';
  if (txt) document.getElementById('syncStat').textContent = txt;
}
function toonStatus() {
  const net = document.getElementById('net');
  net.className = 'dot ' + (navigator.onLine ? 'on' : 'off');
  net.title = navigator.onLine ? 'online' : 'offline';
  document.getElementById('count').textContent = LIB.length ? `${LIB.length}` : '';
  const st = document.getElementById('syncStat');
  if (META) {
    const d = new Date(META.bijgewerkt);
    const dagen = Math.floor((Date.now() - d) / 864e5);
    st.innerHTML = `<b>${META.aantal}</b> LP's op dit toestel<br>Bijgewerkt: <b>${d.toLocaleString('nl-BE')}</b>${dagen >= 7 ? ` <span style="color:var(--maybe)">(${dagen} dagen geleden)</span>` : ''}<br>Covers offline: <b>${LIB.filter(x => x.fp).length}</b> van ${LIB.filter(x => x.heeftThumb).length}${LIB.some(x => x.heeftThumb && !x.fp) ? ' <span style="color:var(--maybe)">(tik “Nu bijwerken” met goede wifi om de rest op te halen)</span>' : ''}<br>Bron: ${esc(META.bron)} · app v${APP_VERSIE}`;
  }
}

/* ───────────────────────── Start ───────────────────────── */
async function start() {
  const q = document.getElementById('q');
  let raf = 0;
  q.addEventListener('input', () => { toonAlles = false; FOTO = null; cancelAnimationFrame(raf); raf = requestAnimationFrame(render); });
  q.addEventListener('keydown', e => { if (e.key === 'Enter') q.blur(); });
  document.getElementById('clear').onclick = () => { q.value = ''; FOTO = null; render(); q.focus(); };
  document.getElementById('btnCam').onclick = openCamera;
  document.getElementById('btnKw').onclick = () => { KW_MODUS = !KW_MODUS; FOTO = null; q.value = ''; toonAlles = false; render(); window.scrollTo(0, 0); };
  document.getElementById('camClose').onclick = stopCamera;
  document.getElementById('camShoot').onclick = neemFoto;
  document.getElementById('camLib').onclick = () => { stopCamera(); document.getElementById('fileCam').click(); };
  document.getElementById('fileCam').onchange = e => { fotoUitBestand(e.target.files[0]); e.target.value = ''; };
  const sheet = document.getElementById('settings');
  document.getElementById('btnSettings').onclick = async () => {
    document.getElementById('url').value = (await DB.get('url')) || '';
    toonStatus(); sheet.classList.add('open');
  };
  document.getElementById('btnClose').onclick = () => sheet.classList.remove('open');
  sheet.addEventListener('click', e => { if (e.target === sheet) sheet.classList.remove('open'); });
  document.getElementById('btnSaveUrl').onclick = async () => {
    const u = document.getElementById('url').value.trim();
    if (u && !/^https:\/\/(script\.google(usercontent)?\.com|docs\.google\.com)\//.test(u)) { toast('Dit lijkt geen Google-link.'); return; }
    if (u && /script\.google/.test(u) && !/[?&]token=/.test(u)) { toast('De link mist nog “?token=…”.'); return; }
    if (u && /docs\.google\.com/.test(u) && !/output=csv/.test(u)) { toast('Kies bij “Publiceren op internet” het formaat CSV (link eindigt op output=csv).'); return; }
    await DB.set('url', u); toast('Link bewaard'); syncKnop();
  };
  const syncKnop = async () => { const b = document.getElementById('btnSync'); b.disabled = true; await syncVanUrl(false); b.disabled = false; };
  document.getElementById('btnSync').onclick = syncKnop;
  document.getElementById('btnFile').onclick = () => document.getElementById('fileImp').click();
  document.getElementById('fileImp').onchange = async e => {
    const f = e.target.files[0]; e.target.value = ''; if (!f) return;
    try { await importeerBestand(f); } catch (err) { setProg(null); toast('Import mislukt: ' + err.message); }
  };
  document.getElementById('btnPreload').onclick = e => ocrKlaarzetten(e.currentTarget);
  window.addEventListener('online', toonStatus);
  window.addEventListener('offline', toonStatus);

  try {
    LIB = (await DB.get('lib')) || [];
    META = (await DB.get('meta')) || null;
  } catch (e) { LIB = []; }
  bouwIndex();
  toonStatus();
  render();
  if ((await DB.get('ocrKlaar'))) document.getElementById('ocrStat').textContent = '✓ Tekstherkenning staat klaar en werkt offline.';

  if (navigator.storage && navigator.storage.persist) navigator.storage.persist().catch(() => {});
  if ('serviceWorker' in navigator) {
    navigator.serviceWorker.register('sw.js').then(reg => {
      reg.addEventListener('updatefound', () => {
        const nw = reg.installing;
        nw && nw.addEventListener('statechange', () => {
          if (nw.state === 'installed' && navigator.serviceWorker.controller) toast('Nieuwe versie geïnstalleerd — sluit de app en open opnieuw.');
        });
      });
    }).catch(() => {});
  }
  // Automatisch bijwerken op de achtergrond als er internet is en de data > 12 u oud is
  const oud = !META || (Date.now() - new Date(META.bijgewerkt)) > 12 * 36e5;
  if (navigator.onLine && oud && (await DB.get('url'))) syncVanUrl(true);
}
start();
