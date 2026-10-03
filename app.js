/* LP-zoeker — offline zoeken in de LP-bibliotheek.
 * Alles draait lokaal op het toestel: de bibliotheek staat in IndexedDB,
 * de app zelf zit in de cache van de service worker. */
'use strict';

const APP_VERSIE = '1.8.0';
const MAX_TONEN = 40;
const THUMB_PX = 112;
const GROOT_PX = 720;

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
const proxyUrl = u => 'https://wsrv.nl/?url=' + encodeURIComponent(u.replace(/^https?:\/\//, '')) + '&w=720&h=720&fit=cover&output=jpg&q=80';
function vierkant(w, h, frac = 1) {
  const s = Math.min(w, h) * frac;
  return [(w - s) / 2, (h - s) / 2, s, s];
}
/** Maakt kleine thumbnail + vingerafdruk van een cover (data-URL of http-URL). */
/** Volledige-resolutie cover uit de Drive-map van de bibliotheek-app. */
const driveUrl = id => 'https://lh3.googleusercontent.com/d/' + encodeURIComponent(id) + '=w' + GROOT_PX;
const driveThumbUrl = id => 'https://drive.google.com/thumbnail?id=' + encodeURIComponent(id) + '&sz=w' + GROOT_PX;
async function verwerkCover(src, fileId) {
  src = (src || '').trim();
  if (!src && !fileId) return { thumb: '', fp: null };
  const pogingen = [];
  if (fileId) pogingen.push(driveUrl(fileId), proxyUrl(driveThumbUrl(fileId)));   // scherpe versie eerst
  if (/^https?:/i.test(src)) pogingen.push(src, proxyUrl(src)); else if (src) pogingen.push(src);
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
      // Grote versie om in te zoomen (max. GROOT_PX, nooit groter dan het origineel)
      const G = Math.round(Math.min(GROOT_PX, rect[2]));
      let groot = '';
      if (G > THUMB_PX * 1.3) {
        const cg = document.createElement('canvas');
        cg.width = cg.height = G;
        const gx = cg.getContext('2d');
        gx.imageSmoothingQuality = 'high';
        gx.drawImage(im, rect[0], rect[1], rect[2], rect[3], 0, 0, G, G);
        groot = cg.toDataURL('image/jpeg', 0.8);
      }
      return { thumb, groot, fp: vingerafdruk(im, rect), drive: !!fileId && pogingen.indexOf(p) < 2 };
    } catch (e) { /* volgende poging */ }
  }
  // Niet lokaal op te slaan: toon enkel online
  return { thumb: /^https?:/i.test(src) ? src : '', groot: '', fp: null };
}
function hashStr(s) { let h = 2166136261; for (let i = 0; i < s.length; i += 7) { h ^= s.charCodeAt(i); h = Math.imul(h, 16777619); } return (h >>> 0).toString(36) + ':' + s.length; }

/* ───────────────────────── Synchroniseren ───────────────────────── */
function rijNaarItem(r, kol) {
  const o = {}; kol.forEach((k, i) => { o[k] = r[i] == null ? '' : String(r[i]); });
  return {
    id: o.id || '', artiest: o.artiest || '', album: o.album || '', jaar: o.jaar || '',
    label: o.label || '', genre: o.genre || '', notities: o.notities || '',
    kringwinkel: o.kringwinkel || '', bron: o.bron || '', _cover: o.cover || '', _fid: (o.coverfileid || '').trim()
  };
}

async function importeerItems(items, bronNaam, progress) {
  // Bestaande vingerafdrukken hergebruiken als de cover niet veranderde
  const oud = new Map();
  LIB.forEach((it, i) => { if (it.ch && it.gv === 2) oud.set(it.ch, { fp: it.fp, key: it.tk, groot: it.heeftGroot, scherp: it.scherp }); });
  const oudeThumbKeys = oud.size ? new Set(await DB.allThumbKeys()) : new Set();
  const oudeThumbs = new Map();
  const nodig = [];
  items.forEach((it, i) => {
    it.tk = 't' + i;
    it.ch = (it._cover || it._fid) ? hashStr(it._fid + '|' + it._cover) : '';
    const o = it.ch && oud.get(it.ch);
    if (o && o.fp && o.key && oudeThumbKeys.has(o.key)) { it.scherp = o.scherp; it.fp = o.fp; it._reuse = o.key; it._reuseG = o.groot; }
    else if (it._cover || it._fid) nodig.push(it);
  });
  // Oude thumbs die we hergebruiken ophalen
  const reuse = items.filter(it => it._reuse);
  for (let k = 0; k < reuse.length; k += 200) {
    const part = reuse.slice(k, k + 200);
    const vals = await DB.thumbs(part.map(it => it._reuse));
    const gvals = await DB.thumbs(part.map(it => it._reuseG ? it._reuse + 'g' : '_geen_'));
    part.forEach((it, j) => { oudeThumbs.set(it.tk, vals[j] || ''); if (gvals[j]) oudeThumbs.set(it.tk + 'g', gvals[j]); });
  }
  const nieuweThumbs = new Map();
  const r_scherp = new Set(items.filter(it => it.scherp && it._reuse).map(it => it.tk));
  let klaar = 0;
  const PAR = 4;
  for (let k = 0; k < nodig.length; k += PAR) {
    await Promise.all(nodig.slice(k, k + PAR).map(async it => {
      const r = await verwerkCover(it._cover, it._fid);
      it.fp = r.fp; if (r.drive) r_scherp.add(it.tk); nieuweThumbs.set(it.tk, r.thumb); if (r.groot) nieuweThumbs.set(it.tk + 'g', r.groot);
    }));
    klaar += Math.min(PAR, nodig.length - k);
    progress && progress(klaar / nodig.length, `Hoezen verwerken ${klaar}/${nodig.length}`);
  }
  const entries = [];
  items.forEach(it => {
    const t = nieuweThumbs.has(it.tk) ? nieuweThumbs.get(it.tk) : oudeThumbs.get(it.tk);
    const g = nieuweThumbs.has(it.tk) ? nieuweThumbs.get(it.tk + 'g') : oudeThumbs.get(it.tk + 'g');
    it.heeftThumb = !!t; it.heeftGroot = !!g; it.gv = 2; it.scherp = !!(g && r_scherp.has(it.tk));
    if (t) entries.push([it.tk, t]);
    if (g) entries.push([it.tk + 'g', g]);
    delete it._cover; delete it._fid; delete it._reuse; delete it._reuseG;
  });
  await DB.putThumbs(entries, true);
  THUMBS.clear();
  const meta = { bijgewerkt: new Date().toISOString(), bron: bronNaam, aantal: items.length, versie: APP_VERSIE };
  await DB.set('lib', items);
  await DB.set('meta', meta);
  LIB = items; META = meta;
  bouwIndex();
}

let SYNC_BEZIG = null, LAATSTE_POGING = 0;
function syncVanUrl(stil) {
  if (SYNC_BEZIG) return SYNC_BEZIG;           // nooit twee tegelijk
  LAATSTE_POGING = Date.now();
  SYNC_BEZIG = _sync(stil).finally(() => { SYNC_BEZIG = null; document.getElementById('net').classList.remove('sync'); });
  return SYNC_BEZIG;
}
/** Automatisch bijwerken (bij opstarten, terugkeren naar de app of wanneer er weer bereik is). */
async function autoSync(minPauze) {
  if (!navigator.onLine || SYNC_BEZIG) return;
  if (Date.now() - LAATSTE_POGING < minPauze) return;
  if (!(await DB.get('url'))) return;
  syncVanUrl(true);
}
async function _sync(stil) {
  const url = (await DB.get('url')) || '';
  if (!url) { if (!stil) toast('Stel eerst de export-link in (⚙︎).'); return false; }
  if (!navigator.onLine) { if (!stil) toast('Geen internet — je werkt verder met de bewaarde bibliotheek.'); return false; }
  setProg(0.02, 'Bibliotheek ophalen…');
  document.getElementById('net').classList.add('sync');
  try {
    const ctrl = new AbortController();
    const to = setTimeout(() => ctrl.abort(), 60000);
    const resp = await fetch(url, { signal: ctrl.signal, cache: 'no-store' });
    clearTimeout(to);
    if (!resp.ok) throw new Error('HTTP ' + resp.status);
    const txt = await resp.text();
    const h = hashStr(txt) + ':' + hashStr(txt.slice(1) + '#');
    if (META && META.hash === h && LIB.length) {       // niets veranderd → niets te doen
      META.bijgewerkt = new Date().toISOString(); await DB.set('meta', META);
      setProg(null);
      if (!stil) toast('✓ Alles was al up-to-date');
      return true;
    }
    const items = parseTekst(txt);
    if (!items.length) throw new Error('Geen LP\'s ontvangen');
    const voor = LIB.length;
    setProg(0.05, `${items.length} LP's ontvangen, hoezen verwerken…`);
    await importeerItems(items, 'Google Sheet', setProg);
    META.hash = h; await DB.set('meta', META);
    setProg(null);
    const verschil = items.length - voor;
    if (!stil) toast(`✓ ${items.length} LP's bijgewerkt`);
    else if (voor && verschil > 0) toast(`✓ Bijgewerkt: ${verschil} nieuwe LP${verschil === 1 ? '' : "'s"}`);
    else if (voor && verschil < 0) toast(`✓ Bijgewerkt (${items.length} LP's)`);
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
    notities: 'notities', opmerkingenkringwinkel: 'kringwinkel', coverurl: 'cover', bronurl: 'bron', coverfileid: 'coverfileid' };
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

/** OCR in twee doorgangen: donkere tekst op lichte achtergrond, en omgekeerd. */
async function leesTekst(cv) {
  const w = await ocrWorker();
  const t1 = (await w.recognize(binariseer(cv, 900, false))).data.text || '';
  const t2 = (await w.recognize(binariseer(cv, 900, true))).data.text || '';
  return t1 + '\n' + t2;
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
      const tekst = await leesTekst(cv);
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
/* Zoom: hardware-zoom van de iPhone als die beschikbaar is (o.a. 0,5× groothoek),
 * anders digitale zoom (enkel inzoomen). */
let CAMZ = { hw: null, min: 1, max: 4, z: 1 };
let CAM_MODUS = 'collectie';
async function openCamera(modus) {
  CAM_MODUS = modus === 'prijs' ? 'prijs' : 'collectie';
  document.querySelector('.camtxt').textContent = CAM_MODUS === 'prijs'
    ? '💶 Prijs: hoes (of achterkant met catalogusnr.) in het kader'
    : 'Hoes binnen het kader · knijp om te zoomen';
  if (CAM_MODUS === 'collectie' && !LIB.length) { toast('Nog geen bibliotheek geladen (⚙︎).'); return; }
  if (CAM_MODUS === 'prijs' && !(await DB.get('discogsToken'))) { toast('Stel eerst je Discogs-token in (⚙︎).'); openSettings(); return; }
  if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia) { document.getElementById('fileCam').click(); return; }
  const cv = document.getElementById('camview');
  const video = document.getElementById('video');
  try {
    // 4:3 = volledige sensor (16:9 snijdt bij, waardoor het beeld "ingezoomd" lijkt)
    stream = await navigator.mediaDevices.getUserMedia({
      video: { facingMode: { ideal: 'environment' }, width: { ideal: 1920 }, height: { ideal: 1440 }, aspectRatio: { ideal: 4 / 3 } },
      audio: false
    });
    video.srcObject = stream;
    cv.classList.add('open');
    await video.play().catch(() => {});
    await initCamZoom();
    plaatsKader();
    ocrWorker().catch(() => {}); // alvast opwarmen
  } catch (e) {
    stopCamera();
    document.getElementById('fileCam').click();
  }
}
async function initCamZoom() {
  const track = stream && stream.getVideoTracks()[0];
  let cap = {};
  try { cap = (track && track.getCapabilities) ? track.getCapabilities() : {}; } catch (e) {}
  if (cap.zoom && cap.zoom.max > cap.zoom.min) {
    CAMZ = { hw: track, min: cap.zoom.min, max: Math.min(cap.zoom.max, 6), z: cap.zoom.min };
  } else {
    CAMZ = { hw: null, min: 1, max: 4, z: 1 };
  }
  await zetCamZoom(CAMZ.min);
  const stappen = [CAMZ.min, 1, 2, 3].filter((v, i, a) => v >= CAMZ.min && v <= CAMZ.max && a.indexOf(v) === i);
  const bar = document.getElementById('zoombar');
  bar.innerHTML = stappen.map(v => `<button data-z="${v}">${String(+v.toFixed(1)).replace('.', ',')}×</button>`).join('');
  bar.querySelectorAll('button').forEach(btn => btn.onclick = () => zetCamZoom(+btn.dataset.z));
  markeerZoom();
}
async function zetCamZoom(z) {
  z = Math.max(CAMZ.min, Math.min(CAMZ.max, z));
  CAMZ.z = z;
  const video = document.getElementById('video');
  if (CAMZ.hw) {
    try { await CAMZ.hw.applyConstraints({ advanced: [{ zoom: z }] }); video.style.transform = ''; }
    catch (e) { CAMZ.hw = null; CAMZ.min = 1; video.style.transform = `scale(${Math.max(1, z)})`; }
  } else {
    video.style.transform = z > 1 ? `scale(${z})` : '';
  }
  markeerZoom();
}
function markeerZoom() {
  document.querySelectorAll('#zoombar button').forEach(b => b.classList.toggle('on', Math.abs(+b.dataset.z - CAMZ.z) < 0.05));
}
/** Zichtbaar videovlak (object-fit: contain) in schermcoördinaten, zonder digitale zoom. */
function videoVlak() {
  const v = document.getElementById('video');
  const vw = v.videoWidth || 4, vh = v.videoHeight || 3;
  const W = v.clientWidth, H = v.clientHeight, sc = Math.min(W / vw, H / vh);
  const L = v.offsetLeft + (W - vw * sc) / 2, T = v.offsetTop + (H - vh * sc) / 2;
  return { L, T, w: vw * sc, h: vh * sc, sc, W, H };
}
function plaatsKader() {
  const g = document.querySelector('.guide');
  const r = videoVlak();
  const s = Math.min(r.w, r.h) * 0.94;
  Object.assign(g.style, { left: (r.L + (r.w - s) / 2) + 'px', top: (r.T + (r.h - s) / 2) + 'px', width: s + 'px', height: s + 'px' });
}
function stopCamera() {
  if (stream) stream.getTracks().forEach(t => t.stop());
  stream = null;
  document.getElementById('video').style.transform = '';
  document.getElementById('camview').classList.remove('open');
}
function neemFoto() {
  const video = document.getElementById('video');
  const vw = video.videoWidth, vh = video.videoHeight;
  if (!vw) return;
  const r = videoVlak();
  const dz = CAMZ.hw ? 1 : Math.max(1, CAMZ.z);              // digitale zoom: kader beslaat kleiner deel
  const g = document.querySelector('.guide').getBoundingClientRect();
  const cv = document.getElementById('camview').getBoundingClientRect();
  const cx = r.L + r.w / 2, cy = r.T + r.h / 2;              // zoom-centrum (schermcoörd. binnen camview)
  const gx = g.left - cv.left, gy = g.top - cv.top;
  let sx = ((cx + (gx - cx) / dz) - r.L) / r.sc;
  let sy = ((cy + (gy - cy) / dz) - r.T) / r.sc;
  let s = (g.width / dz) / r.sc;
  s = Math.min(s, vw, vh); sx = Math.max(0, Math.min(vw - s, sx)); sy = Math.max(0, Math.min(vh - s, sy));
  const snap = document.createElement('canvas');
  snap.width = vw; snap.height = vh;
  snap.getContext('2d').drawImage(video, 0, 0, vw, vh);
  stopCamera();
  (CAM_MODUS === 'prijs' ? verwerkPrijsFoto : verwerkFoto)(snap, [sx, sy, s, s]);
}
function initCamGebaren() {
  const cvw = document.getElementById('camview');
  let st = null;
  const afst = t => Math.hypot(t[0].clientX - t[1].clientX, t[0].clientY - t[1].clientY);
  cvw.addEventListener('touchstart', e => { if (e.touches.length === 2) st = { d: afst(e.touches), z: CAMZ.z }; }, { passive: true });
  cvw.addEventListener('touchmove', e => {
    if (!st || e.touches.length !== 2) return;
    e.preventDefault();
    zetCamZoom(st.z * afst(e.touches) / st.d);
  }, { passive: false });
  cvw.addEventListener('touchend', e => { if (e.touches.length < 2) st = null; });
  window.addEventListener('resize', () => { if (stream) plaatsKader(); });
  document.getElementById('video').addEventListener('loadedmetadata', () => { if (stream) plaatsKader(); });
}
async function fotoUitBestand(file) {
  if (!file) return;
  try {
    const url = URL.createObjectURL(file);
    const im = await laadImg(url);
    await (CAM_MODUS === 'prijs' ? verwerkPrijsFoto : verwerkFoto)(im, vierkant(im.naturalWidth, im.naturalHeight, 0.92));
    URL.revokeObjectURL(url);
  } catch (e) { toast('Foto kon niet gelezen worden.'); }
}

/* ───────────────────────── Weergave ───────────────────────── */
let FOTO = null;
let KW_MODUS = false;
let PRIJS = null;
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
    <img data-tk="${esc(it.heeftThumb ? it.tk : '')}" data-groot="${it.heeftGroot ? 1 : ''}" data-titel="${esc((it.artiest || '') + ' — ' + (it.album || ''))}" alt="" class="zoombaar" style="${it.heeftThumb ? '' : 'display:none'}">
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
  if (PRIJS && !q.trim()) return renderPrijs(out);
  if (!LIB.length) {
    out.innerHTML = `<div class="empty"><div class="big">💿</div>Nog geen bibliotheek op dit toestel.<br><br>
      Tik op <b>⚙︎</b> om de export-link in te stellen en de bibliotheek op te halen (één keer met internet).</div>`;
    return;
  }
  zetKwKnop();
  if (KW_MODUS) return renderKw(out, q);
  if (PRIJS && !q.trim()) return renderPrijs(out);
  PRIJS = null;
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
  html += `<img class="shot" src="${shot}" data-titel="Jouw foto" alt="">`;
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

/* ───────────────────────── Discogs-prijzen ───────────────────────── */
const DG = 'https://api.discogs.com';
const STATEN = [['Mint (M)', 'M'], ['Near Mint (NM or M-)', 'NM'], ['Very Good Plus (VG+)', 'VG+'], ['Very Good (VG)', 'VG'],
  ['Good Plus (G+)', 'G+'], ['Good (G)', 'G'], ['Fair (F)', 'F'], ['Poor (P)', 'P']];
const PRIJS_CACHE = new Map();

async function dgFetch(pad, params) {
  const token = await DB.get('discogsToken');
  if (!token) throw new Error('Geen Discogs-token ingesteld (⚙︎)');
  const u = new URL(DG + pad);
  Object.entries(params || {}).forEach(([k, v]) => { if (v !== '' && v != null) u.searchParams.set(k, v); });
  const ctrl = new AbortController(); const to = setTimeout(() => ctrl.abort(), 20000);
  try {
    const r = await fetch(u, { headers: { Authorization: 'Discogs token=' + token }, signal: ctrl.signal });
    if (r.status === 401) throw new Error('Discogs-token ongeldig (⚙︎)');
    if (r.status === 429) throw new Error('Even te veel opzoekingen — wacht een minuutje');
    const j = await r.json().catch(() => ({}));
    if (!r.ok) { const e = new Error(j.message || ('Discogs HTTP ' + r.status)); e.status = r.status; throw e; }
    return j;
  } catch (e) {
    if (e.name === 'AbortError') throw new Error('Discogs antwoordt niet (time-out)');
    if (e instanceof TypeError) throw new Error('Geen verbinding met Discogs');
    throw e;
  } finally { clearTimeout(to); }
}
async function munt() { return (await DB.get('discogsMunt')) || 'EUR'; }

/** Haalt uit de gelezen tekst: barcode, catalogusnummers en bruikbare woorden. */
function zoekTermen(tekst) {
  const t = String(tekst || '');
  const barcode = (t.replace(/[ \-]/g, '').match(/\b\d{12,13}\b/) || [])[0] || '';
  // Catalogusnummers zoals "SHVL 804", "2C 068-04231", "CBS 62345", "PL 12345"
  const catnos = [...new Set((t.match(/\b[A-Z]{1,6}[ .\-]?\d[\d .\-]{2,10}\d\b/g) || [])
    .map(c => c.trim().replace(/\s+/g, ' ')).filter(c => c.replace(/\D/g, '').length >= 3 && c.replace(/\D/g, '').length <= 10))].slice(0, 3);
  const woorden = [];
  const gezien = new Set();
  String(t).split(/[\s|]+/).forEach(w => {
    const n = norm(w);
    if (!n || n.includes(' ')) { n.split(' ').forEach(x => voegToe(x)); return; }
    voegToe(n);
  });
  function voegToe(n) {
    if (!n || gezien.has(n)) return;
    if (n.length < 3 && !/^(ac|dc|ub|xx)$/.test(n)) return;
    if (/\d/.test(n)) return;
    if (!/[aeiouy]/.test(n) && n.length > 4) return;               // klinkerloze rommel
    if (/(.)\1\1/.test(n)) return;                                   // "lll", "eee"
    if (STOP.has(n) && !['the'].includes(n)) return;
    gezien.add(n); woorden.push(n);
  }
  return { barcode, catnos, woorden: woorden.slice(0, 10) };
}

async function dgZoek(query) {
  const basis = { type: 'release', format: 'Vinyl', per_page: 25 };
  if (query.barcode) {
    const r = await dgFetch('/database/search', { ...basis, barcode: query.barcode });
    if (r.results && r.results.length) return { res: r.results, via: 'barcode ' + query.barcode };
  }
  for (const c of query.catnos || []) {
    if (query.artiest) {
      const r = await dgFetch('/database/search', { ...basis, catno: c, artist: query.artiest });
      if (r.results && r.results.length) return { res: r.results, via: 'catalogusnr. ' + c + ' + artiest' };
    }
    const r = await dgFetch('/database/search', { ...basis, catno: c });
    if (r.results && r.results.length && r.results.length < 25) return { res: r.results, via: 'catalogusnr. ' + c };
  }
  if (query.artiest && query.titel) {
    const r = await dgFetch('/database/search', { ...basis, artist: query.artiest, release_title: query.titel });
    if (r.results && r.results.length) return { res: r.results, via: 'artiest + titel' };
  }
  if (query.artiest || query.titel) {
    const q = [query.artiest, query.titel].filter(Boolean).join(' ');
    const r = await dgFetch('/database/search', { ...basis, q });
    if (r.results && r.results.length) return { res: r.results, via: '“' + q + '”' };
  }
  const w = query.woorden || [];
  const pogingen = [w.slice(0, 7), w.slice(0, 5), [...w].sort((a, b) => b.length - a.length).slice(0, 3), w.slice(0, 2)]
    .map(x => x.join(' ')).filter((x, i, a) => x && a.indexOf(x) === i);
  for (const q of pogingen) {
    const r = await dgFetch('/database/search', { ...basis, q });
    if (r.results && r.results.length) return { res: r.results, via: '“' + q + '”' };
  }
  return { res: [], via: '' };
}

/** Sorteert resultaten mee op gelijkenis met de foto (helpt de juiste persing te vinden). */
async function rangschikOpHoes(res, fp) {
  if (!fp) return res;
  await Promise.all(res.slice(0, 20).map(async (r, k) => {
    r._rang = k;
    const src = r.cover_image || r.thumb;
    if (!src || /spacer/.test(src)) return;
    try {
      const im = await laadImg(proxyUrl(src), 8000);
      r._d = fpAfstand(fp, vingerafdruk(im, vierkant(im.naturalWidth, im.naturalHeight)));
    } catch (e) {}
  }));
  return res.map((r, k) => ({ r, s: (r._d != null ? r._d * 2.2 : 1.1) + Math.min(k, 20) * 0.025 }))
    .sort((a, b) => a.s - b.s).map(x => x.r);
}

async function haalPrijzen(id) {
  if (PRIJS_CACHE.has(id)) return PRIJS_CACHE.get(id);
  const curr = await munt();
  const [rel, stats, sugg] = await Promise.all([
    dgFetch('/releases/' + id, { curr_abbr: curr }).catch(e => ({ _fout: e.message })),
    dgFetch('/marketplace/stats/' + id, { curr_abbr: curr }).catch(e => ({ _fout: e.message })),
    dgFetch('/marketplace/price_suggestions/' + id).catch(e => ({ _fout: e.message, _status: e.status }))
  ]);
  const d = { id, rel, stats, sugg, curr, t: Date.now() };
  PRIJS_CACHE.set(id, d);
  return d;
}

function bedrag(v, c) {
  if (v == null || isNaN(v)) return '—';
  try { return new Intl.NumberFormat('nl-BE', { style: 'currency', currency: c || 'EUR' }).format(v); }
  catch (e) { return (+v).toFixed(2) + ' ' + (c || ''); }
}

/** Kijkt of een Discogs-resultaat al in de eigen collectie zit. */
function inCollectie(titel) {
  const [art, ...rest] = String(titel || '').split(' - ');
  const a = norm(art.replace(/\(\d+\)/g, '')), b = norm(rest.join(' - '));
  if (!a || !b) return null;
  return LIB.find(it => (it._na === a || it._na.includes(a) || a.includes(it._na)) && it._na && it._nb &&
    (it._nb === b || it._nb.includes(b) || b.includes(it._nb))) || null;
}

/* Herkenning met Claude (optioneel, eigen API-sleutel; enkel online gebruikt). */
const CLAUDE_PROMPT = `Dit is een foto van een vinyl-platenhoes (voorkant, achterkant of label) in een tweedehandswinkel.
Lees zorgvuldig wat er staat en geef ENKEL een JSON-object terug, zonder uitleg, met deze velden:
{"artiest": "", "titel": "", "label": "", "catno": "", "barcode": "", "jaar": "", "land": "", "zeker": 0.0}
- "catno" = catalogusnummer precies zoals gedrukt (bv. "SHVL 804", "2C 068-04231"), leeg als niet zichtbaar
- "barcode" = enkel de cijfers onder een streepjescode, anders leeg
- Vul alleen in wat je echt kan lezen of met grote zekerheid herkent; anders een lege string
- "zeker" = je zekerheid (0-1) dat artiest + titel kloppen`;
async function herkenMetClaude(dataUrl) {
  const key = await DB.get('claudeKey');
  if (!key) return null;
  const model = (await DB.get('claudeModel')) || 'claude-sonnet-5';
  const ctrl = new AbortController(); const to = setTimeout(() => ctrl.abort(), 30000);
  try {
    const r = await fetch('https://api.anthropic.com/v1/messages', {
      method: 'POST', signal: ctrl.signal,
      headers: { 'content-type': 'application/json', 'x-api-key': key, 'anthropic-version': '2023-06-01',
        'anthropic-dangerous-direct-browser-access': 'true' },
      body: JSON.stringify({ model, max_tokens: 400, messages: [{ role: 'user', content: [
        { type: 'image', source: { type: 'base64', media_type: 'image/jpeg', data: dataUrl.split(',')[1] } },
        { type: 'text', text: CLAUDE_PROMPT }] }] })
    });
    const j = await r.json().catch(() => ({}));
    if (!r.ok) throw new Error((j.error && j.error.message) || ('Claude HTTP ' + r.status));
    const txt = (j.content || []).map(c => c.text || '').join('');
    const m = txt.match(/\{[\s\S]*\}/);
    if (!m) throw new Error('Onverwacht antwoord van Claude');
    const o = JSON.parse(m[0]);
    Object.keys(o).forEach(k => { if (typeof o[k] === 'string') o[k] = o[k].trim(); });
    return o;
  } finally { clearTimeout(to); }
}

async function verwerkPrijsFoto(src, rect) {
  const cv = document.createElement('canvas');
  const S = 1100; cv.width = cv.height = S;
  cv.getContext('2d').drawImage(src, rect[0], rect[1], rect[2], rect[3], 0, 0, S, S);
  const shot = cv.toDataURL('image/jpeg', 0.6);
  const fp = vingerafdruk(cv, [0, 0, S, S]);
  document.getElementById('q').value = '';
  FOTO = null; KW_MODUS = false;
  let termen = { barcode: '', catnos: [], woorden: [] }, claude = null, claudeFout = '';
  if (navigator.onLine && (await DB.get('claudeKey'))) {
    toonBusy('Hoes lezen met Claude…');
    try { claude = await herkenMetClaude(cv.toDataURL('image/jpeg', 0.85)); }
    catch (e) { claudeFout = e.name === 'AbortError' ? 'time-out' : e.message; }
  }
  if (claude && (claude.artiest || claude.titel || claude.catno || claude.barcode)) {
    termen = { artiest: claude.artiest, titel: claude.titel, label: claude.label,
      catnos: claude.catno ? [claude.catno] : [], barcode: (claude.barcode || '').replace(/\D/g, ''),
      woorden: toks([claude.artiest, claude.titel].join(' ')) };
  } else {
    toonBusy('Tekst lezen…');
    let tekst = '';
    try { tekst = await leesTekst(cv); } catch (e) {}
    termen = zoekTermen(tekst);
  }
  verbergBusy();
  const query = termen.artiest || termen.titel ? [termen.artiest, termen.titel].filter(Boolean).join(' – ') : termen.woorden.slice(0, 6).join(' ');
  PRIJS = { shot, fp, termen, query, status: 'zoeken', res: [], open: null, claude, claudeFout };
  if (!navigator.onLine) {
    await bewaarInWachtrij(PRIJS);
    PRIJS.status = 'offline';
    render(); return;
  }
  render();
  await prijsZoek(termen);
}
function verbergBus() { verbergBusy(); }

async function prijsZoek(termen) {
  const P = PRIJS; if (!P) return;
  P.status = 'zoeken'; P.fout = ''; render();
  try {
    const { res, via } = await dgZoek(termen);
    if (PRIJS !== P) return;
    P.via = via;
    P.res = await rangschikOpHoes(res, P.fp);
    P.status = 'klaar';
    if (P.res[0]) { P.open = P.res[0].id; render(); await toonPrijs(P.res[0].id); }
    else render();
  } catch (e) {
    if (PRIJS !== P) return;
    P.status = 'fout'; P.fout = e.message; render();
  }
}
async function toonPrijs(id) {
  const P = PRIJS; if (!P) return;
  P.open = id; render();
  try { await haalPrijzen(id); } catch (e) { P.fout = e.message; }
  if (PRIJS === P) render();
}

function prijsBlok(d) {
  if (!d) return `<div class="pbox"><div class="spin sm"></div> Prijzen ophalen…</div>`;
  const c = d.curr;
  const st = d.stats || {}, rel = d.rel || {};
  const laagsteNu = st.lowest_price ? bedrag(st.lowest_price.value, st.lowest_price.currency || c) : (rel.lowest_price != null ? bedrag(rel.lowest_price, c) : '—');
  const aantal = st.num_for_sale != null ? st.num_for_sale : rel.num_for_sale;
  let html = `<div class="pbox">`;
  const sg = d.sugg && !d.sugg._fout ? d.sugg : null;
  const waarden = sg ? STATEN.map(([k, kort]) => sg[k] ? { kort, v: sg[k].value, c: sg[k].currency } : null).filter(Boolean) : [];
  const nuV = st.lowest_price ? st.lowest_price.value : rel.lowest_price;
  const advies = k => { const x = waarden.find(w => w.kort === k); return x ? bedrag(x.v, x.c || c) : '—'; };
  html += `<div class="ptrio">
      <div><small>Laagste</small><b>${nuV != null ? bedrag(nuV, (st.lowest_price || {}).currency || c) : '—'}</b><i>nu te koop</i></div>
      <div class="mid"><small>Midden</small><b>${advies('VG+')}</b><i>advies VG+</i></div>
      <div><small>Hoog</small><b>${advies('NM')}</b><i>advies NM</i></div></div>`;
  if (waarden.length) {
    html += `<div class="psub">Discogs-prijsadvies per staat (gebaseerd op verkopen):</div>
      <div class="pgrid">${waarden.map(x => `<span>${x.kort}</span><b>${bedrag(x.v, x.c || c)}</b>`).join('')}</div>`;
  } else {
    const r = d.sugg && d.sugg._fout || '';
    html += `<div class="psub">Geen prijsadvies beschikbaar${/seller|setting|instellingen/i.test(r) ? ' — vul eerst je verkopersinstellingen in op Discogs' : r ? ' (' + esc(r) + ')' : ' (te weinig verkopen)'}.</div>`;
  }
  html += `<div class="pnow">🛒 <b>${aantal != null ? aantal : '—'}</b> exemplaren te koop vanaf <b>${laagsteNu}</b>`;
  if (rel.community) html += ` · ❤︎ ${rel.community.want} willen / ${rel.community.have} hebben`;
  html += `</div>
    <a class="plink" href="https://www.discogs.com/release/${d.id}" target="_blank" rel="noopener">Verkoopgeschiedenis (laag / mediaan / hoog) op Discogs ↗</a>
  </div>`;
  return html;
}

function renderPrijs(out) {
  const P = PRIJS;
  let html = '';
  if (P.shot) html += `<img class="shot" src="${P.shot}" data-titel="Jouw foto" alt="">`;
  html += `<div class="sect">💶 Prijs opzoeken op Discogs</div>
    <form class="pq" id="pqForm"><input id="pq" type="search" value="${esc(P.query)}" placeholder="artiest, titel of catalogusnr." autocomplete="off" autocorrect="off" spellcheck="false"><button>Zoek</button></form>`;
  if (P.claude) {
    const c = P.claude;
    html += `<div class="meta" style="font-size:12.5px;margin-top:6px;color:#cfe5ff">🤖 Claude las: ${esc([c.artiest, c.titel].filter(Boolean).join(' – ') || '—')}${c.catno ? ' · ' + esc(c.catno) : ''}${c.zeker !== undefined && c.zeker < 0.6 ? ' <span style="color:var(--maybe)">(onzeker)</span>' : ''}</div>`;
  } else if (P.claudeFout) {
    html += `<div class="meta" style="font-size:12.5px;margin-top:6px;color:var(--maybe)">Claude niet gelukt (${esc(P.claudeFout)}) — gewone tekstherkenning gebruikt</div>`;
  }
  if (P.via) html += `<div class="meta" style="color:var(--dim);font-size:12.5px;margin-top:4px">Gevonden via ${esc(P.via)}</div>`;
  html += `<div class="meta" style="color:var(--dim);font-size:12.5px;margin-top:4px">Fout gelezen? Tik in het zoekveld → <b>Scan tekst</b> (iPhone) en richt op titel of catalogusnr.</div>`;
  html += `<div style="clear:both"></div>`;
  if (P.status === 'offline') {
    html += `<div class="verdict v-maybe"><span class="big">📶</span><div>Geen internet<small>Foto bewaard in de prijs-wachtrij. Zodra je bereik hebt kan je hem opzoeken via ⏳ hieronder.</small></div></div>`;
  } else if (P.status === 'zoeken') {
    html += `<div class="pbox"><div class="spin sm"></div> Zoeken op Discogs…</div>`;
  } else if (P.status === 'fout') {
    html += `<div class="verdict v-no"><span class="big">!</span><div>Opzoeken mislukt<small>${esc(P.fout)}</small></div></div>`;
  } else if (!P.res.length) {
    html += `<div class="verdict v-no"><span class="big">✗</span><div>Niets gevonden op Discogs<small>Pas de zoektekst hierboven aan (bv. artiest + titel), of fotografeer de achterkant met het catalogusnummer.</small></div></div>`;
  } else {
    html += `<div class="sect">Kies de juiste persing (${P.res.length})</div>`;
    html += P.res.slice(0, 15).map(r => {
      const open = P.open === r.id;
      const eigen = inCollectie(r.title);
      const meta = [r.year, r.country, (r.label || [])[0], r.catno].filter(Boolean).map(esc).join(' · ');
      const fmt = (r.format || []).filter(f => !/^vinyl$/i.test(f)).slice(0, 4).map(esc).join(', ');
      return `<div class="card pres${open ? ' open' : ''}" data-id="${r.id}">
        <img src="${esc(r.thumb || '')}" alt="" class="zoombaar" data-titel="${esc(r.title)}" ${r.cover_image ? `data-src-groot="${esc(r.cover_image)}"` : ''}>
        <div class="body"><div class="art">${esc(r.title)}${eigen ? '<span class="pill dup">✓ in collectie</span>' : ''}</div>
          <div class="meta">${meta}</div>${fmt ? `<div class="meta">${fmt}</div>` : ''}
          ${open ? prijsBlok(PRIJS_CACHE.get(r.id)) : `<div class="meta" style="color:var(--acc)">Tik voor prijzen</div>`}
        </div></div>`;
    }).join('');
  }
  html += `<button class="more" id="prijsNieuw">📷 Nieuwe prijsfoto</button>`;
  out.innerHTML = html;
  document.getElementById('pqForm').onsubmit = e => {
    e.preventDefault();
    const v = document.getElementById('pq').value.trim(); if (!v) return;
    document.getElementById('pq').blur();
    P.query = v; P.via = '';
    const t = zoekTermen(v); t.woorden = toks(v).filter(w => w.length > 1);
    const delen = v.split(/\s+[–—-]\s+/);
    if (delen.length === 2) { t.artiest = delen[0].trim(); t.titel = delen[1].trim(); }
    if (/\d{3,}/.test(v) && t.woorden.length <= 1) t.catnos = [v];
    prijsZoek(t);
  };
  out.querySelectorAll('.card.pres').forEach(c => c.addEventListener('click', e => {
    if (e.target.closest('a,img')) return;
    const id = +c.dataset.id; if (P.open !== id || !PRIJS_CACHE.has(id)) toonPrijs(id);
  }));
  document.getElementById('prijsNieuw').onclick = () => openCamera('prijs');
}

/* Prijs-wachtrij (foto's genomen zonder internet) */
async function bewaarInWachtrij(P) {
  const q = (await DB.get('prijsWachtrij')) || [];
  q.unshift({ t: Date.now(), shot: P.shot, fp: P.fp, termen: P.termen, query: P.query });
  await DB.set('prijsWachtrij', q.slice(0, 30));
  zetWachtKnop();
}
async function zetWachtKnop() {
  const q = (await DB.get('prijsWachtrij')) || [];
  const b = document.getElementById('btnWacht');
  b.style.display = q.length ? '' : 'none';
  b.innerHTML = `⏳ Prijzen <span>${q.length}</span>`;
}
async function toonWachtrij() {
  const q = (await DB.get('prijsWachtrij')) || [];
  const out = document.getElementById('out');
  KW_MODUS = false; FOTO = null; PRIJS = null; document.getElementById('q').value = ''; zetKwKnop();
  out.innerHTML = `<div class="verdict v-maybe"><span class="big">⏳</span><div>Prijs-wachtrij (${q.length})<small>Foto's genomen zonder internet. Tik er één aan om de prijs op te zoeken${navigator.onLine ? '' : ' (zodra er bereik is)'}.</small></div></div>` +
    q.map((x, k) => `<div class="card wq" data-k="${k}"><img src="${x.shot}" alt=""><div class="body">
      <div class="art">${esc(x.query || '(geen tekst gelezen)')}</div>
      <div class="meta">${new Date(x.t).toLocaleString('nl-BE')}</div>
      <div class="meta" style="color:var(--acc)">Tik om op te zoeken · <span class="wqdel" data-k="${k}">verwijderen</span></div></div></div>`).join('');
  out.querySelectorAll('.card.wq').forEach(c => c.onclick = async e => {
    const k = +c.dataset.k;
    const lijst = (await DB.get('prijsWachtrij')) || [];
    const x = lijst[k]; if (!x) return;
    lijst.splice(k, 1); await DB.set('prijsWachtrij', lijst); zetWachtKnop();
    if (e.target.classList.contains('wqdel')) { toonWachtrij(); return; }
    if (!navigator.onLine) { lijst.splice(k, 0, x); await DB.set('prijsWachtrij', lijst); zetWachtKnop(); toast('Nog geen internet.'); return; }
    let termen = x.termen, query = x.query, claude = null, claudeFout = '';
    if (await DB.get('claudeKey')) {
      toonBusy('Hoes lezen met Claude…');
      try { claude = await herkenMetClaude(x.shot); } catch (err) { claudeFout = err.message; }
      verbergBusy();
      if (claude && (claude.artiest || claude.titel || claude.catno)) {
        termen = { artiest: claude.artiest, titel: claude.titel, catnos: claude.catno ? [claude.catno] : [],
          barcode: (claude.barcode || '').replace(/\D/g, ''), woorden: toks([claude.artiest, claude.titel].join(' ')) };
        query = [claude.artiest, claude.titel].filter(Boolean).join(' – ');
      }
    }
    PRIJS = { shot: x.shot, fp: x.fp, termen, query, status: 'zoeken', res: [], open: null, claude, claudeFout };
    render(); prijsZoek(termen);
  });
  window.scrollTo(0, 0);
}

/* ───────────────────────── Vergroten ───────────────────────── */
async function toonGroot(img) {
  const z = document.getElementById('zoom'), zi = document.getElementById('zoomImg');
  zi.src = img.src;                                  // meteen iets tonen
  document.getElementById('zoomTxt').textContent = img.dataset.titel || '';
  resetZoom(); z.classList.add('open');
  if (img.dataset.srcGroot) { zi.src = img.dataset.srcGroot; }
  else if (img.dataset.tk && img.dataset.groot) {
    try { const [g] = await DB.thumbs([img.dataset.tk + 'g']); if (g && z.classList.contains('open')) zi.src = g; } catch (e) {}
  }
}
let ZS = { s: 1, x: 0, y: 0 };
function resetZoom() { ZS = { s: 1, x: 0, y: 0 }; zetZoom(); }
function zetZoom() { document.getElementById('zoomImg').style.transform = `translate(${ZS.x}px,${ZS.y}px) scale(${ZS.s})`; }
function initZoom() {
  const z = document.getElementById('zoom'), zi = document.getElementById('zoomImg');
  let start = null, laatsteTik = 0, beweegd = false;
  const afst = t => Math.hypot(t[0].clientX - t[1].clientX, t[0].clientY - t[1].clientY);
  z.addEventListener('touchstart', e => {
    beweegd = false;
    const t = e.touches;
    start = t.length === 2 ? { d: afst(t), s: ZS.s, x: ZS.x, y: ZS.y }
      : { px: t[0].clientX, py: t[0].clientY, x: ZS.x, y: ZS.y, s: ZS.s };
  }, { passive: true });
  z.addEventListener('touchmove', e => {
    if (!start) return; e.preventDefault(); beweegd = true;
    const t = e.touches;
    if (t.length === 2 && start.d) ZS.s = Math.max(1, Math.min(5, start.s * afst(t) / start.d));
    else if (t.length === 1 && ZS.s > 1 && start.px != null) { ZS.x = start.x + t[0].clientX - start.px; ZS.y = start.y + t[0].clientY - start.py; }
    zetZoom();
  }, { passive: false });
  z.addEventListener('touchend', e => { if (e.touches.length === 0) { if (ZS.s <= 1.02) resetZoom(); start = null; } });
  z.addEventListener('click', e => {
    if (beweegd) return;
    if (e.target.id === 'zoomClose') { z.classList.remove('open'); return; }
    const nu = Date.now();
    if (nu - laatsteTik < 320) { ZS.s > 1 ? resetZoom() : (ZS = { s: 2.5, x: 0, y: 0 }, zetZoom()); laatsteTik = 0; return; }
    laatsteTik = nu;
    setTimeout(() => { if (laatsteTik === nu && ZS.s <= 1 && e.target !== zi) z.classList.remove('open'); }, 330);
  });
  document.getElementById('out').addEventListener('click', e => {
    const im = e.target.closest('img.zoombaar, img.shot');
    if (im && im.src) toonGroot(im);
  });
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
    st.innerHTML = `<b>${META.aantal}</b> LP's op dit toestel<br>Bijgewerkt: <b>${d.toLocaleString('nl-BE')}</b>${dagen >= 7 ? ` <span style="color:var(--maybe)">(${dagen} dagen geleden)</span>` : ''}<br>Covers offline: <b>${LIB.filter(x => x.fp).length}</b> van ${LIB.filter(x => x.heeftThumb).length} · scherp (Drive): <b>${LIB.filter(x => x.scherp).length}</b>${LIB.some(x => x.heeftThumb && !x.fp) ? ' <span style="color:var(--maybe)">(tik “Nu bijwerken” met goede wifi om de rest op te halen)</span>' : ''}<br>Bron: ${esc(META.bron)} · app v${APP_VERSIE}`;
  }
}

/* ───────────────────────── Start ───────────────────────── */
async function start() {
  const q = document.getElementById('q');
  let raf = 0;
  q.addEventListener('input', () => { toonAlles = false; FOTO = null; cancelAnimationFrame(raf); raf = requestAnimationFrame(render); });
  q.addEventListener('keydown', e => { if (e.key === 'Enter') q.blur(); });
  document.getElementById('clear').onclick = () => { q.value = ''; FOTO = null; render(); q.focus(); };
  initZoom();
  initCamGebaren();
  document.getElementById('btnCam').onclick = () => openCamera('collectie');
  document.getElementById('btnPrijs').onclick = () => openCamera('prijs');
  document.getElementById('btnWacht').onclick = toonWachtrij;
  zetWachtKnop();
  document.getElementById('btnClSave').onclick = async () => {
    const k = document.getElementById('clKey').value.trim();
    await DB.set('claudeKey', k); await DB.set('claudeModel', document.getElementById('clModel').value);
    toast(k ? '✓ Claude-sleutel bewaard' : 'Claude-sleutel gewist');
  };
  document.getElementById('btnDgSave').onclick = async () => {
    const t = document.getElementById('dgToken').value.trim();
    await DB.set('discogsToken', t);
    await DB.set('discogsMunt', document.getElementById('dgMunt').value);
    PRIJS_CACHE.clear();
    if (!t) { toast('Discogs-token gewist'); return; }
    try { const me = await dgFetch('/oauth/identity'); toast('✓ Verbonden met Discogs als ' + me.username); document.getElementById('dgStat').textContent = '✓ Verbonden als ' + me.username; }
    catch (e) { toast('Bewaard, maar controle mislukt: ' + e.message); }
  };
  document.getElementById('btnKw').onclick = () => { KW_MODUS = !KW_MODUS; FOTO = null; q.value = ''; toonAlles = false; render(); window.scrollTo(0, 0); };
  document.getElementById('camClose').onclick = stopCamera;
  document.getElementById('camShoot').onclick = neemFoto;
  document.getElementById('camLib').onclick = () => { stopCamera(); document.getElementById('fileCam').click(); };
  document.getElementById('fileCam').onchange = e => { fotoUitBestand(e.target.files[0]); e.target.value = ''; };
  const sheet = document.getElementById('settings');
  document.getElementById('btnSettings').onclick = () => window.openSettings();
  window.openSettings = async () => {
    document.getElementById('dgToken').value = (await DB.get('discogsToken')) || '';
    document.getElementById('dgMunt').value = await munt();
    document.getElementById('clKey').value = (await DB.get('claudeKey')) || '';
    document.getElementById('clModel').value = (await DB.get('claudeModel')) || 'claude-sonnet-5';
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
  // Automatisch bijwerken: bij opstarten, bij terugkeren naar de app en zodra er weer bereik is
  autoSync(0);
  document.addEventListener('visibilitychange', () => { if (document.visibilityState === 'visible') autoSync(2 * 60e3); });
  window.addEventListener('online', () => setTimeout(() => autoSync(15e3), 1500));
}
start();
