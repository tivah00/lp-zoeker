/* Service worker: houdt de app volledig offline beschikbaar. */
const SHELL = 'lpz-shell-v1.2.0';
const OCR = 'lpz-ocr-v5';   // apart, zodat app-updates de 7 MB niet opnieuw laden

const SHELL_FILES = ['./', 'index.html', 'app.js', 'manifest.webmanifest',
  'icons/icon-180.png', 'icons/icon-192.png', 'icons/icon-512.png'];
const OCR_FILES = ['tesseract.min.js', 'worker.min.js', 'tesseract-core-simd-lstm.wasm.js', 'eng.traineddata.gz']
  .map(f => 'vendor/ocr/' + f);

self.addEventListener('install', e => {
  e.waitUntil((async () => {
    const c = await caches.open(SHELL);
    await c.addAll(SHELL_FILES);
    // OCR-bestanden proberen mee te nemen; mislukt dit, dan gebeurt het later bij gebruik
    try {
      const o = await caches.open(OCR);
      const missing = [];
      for (const f of OCR_FILES) if (!(await o.match(f))) missing.push(f);
      if (missing.length) await o.addAll(missing);
    } catch (err) { /* niet fataal */ }
    self.skipWaiting();
  })());
});

self.addEventListener('activate', e => {
  e.waitUntil((async () => {
    const keys = await caches.keys();
    await Promise.all(keys.filter(k => k !== SHELL && k !== OCR).map(k => caches.delete(k)));
    await self.clients.claim();
  })());
});

self.addEventListener('fetch', e => {
  const req = e.request;
  if (req.method !== 'GET') return;
  const url = new URL(req.url);
  if (url.origin !== self.location.origin) return; // Google-export e.d. niet onderscheppen

  const isOcr = url.pathname.includes('/vendor/ocr/');
  e.respondWith((async () => {
    const cacheName = isOcr ? OCR : SHELL;
    const cache = await caches.open(cacheName);
    const hit = await cache.match(req, { ignoreSearch: true }) ||
      (req.mode === 'navigate' ? await cache.match('index.html') : null);
    if (hit) return hit;
    try {
      const resp = await fetch(req);
      if (resp.ok) cache.put(req, resp.clone());
      return resp;
    } catch (err) {
      if (req.mode === 'navigate') {
        const idx = await cache.match('index.html');
        if (idx) return idx;
      }
      return new Response('Offline en niet in cache', { status: 503 });
    }
  })());
});
