// Speichert die App-Dateien, damit Raschel auch offline läuft.
// Die Versionsnummer steht in version.js.
importScripts('version.js');

const CACHE = `raschel-v${APP_VERSION}`;
const ASSETS = [
  './',
  'index.html',
  'style.css',
  'version.js',
  'data/bigrams.js',
  'app.js',
  'manifest.webmanifest',
  'icons/icon-192.png',
  'icons/icon-512.png',
  'icons/apple-touch-icon.png',
];
const WORDS = 'data/words.txt'; // groß und selten geändert: wird einmal geladen und dann gespeichert

self.addEventListener('install', (event) => {
  event.waitUntil(caches.open(CACHE).then((cache) => cache.addAll(ASSETS)));
  self.skipWaiting();
});

self.addEventListener('activate', (event) => {
  event.waitUntil(
    caches.keys().then((keys) =>
      Promise.all(keys.filter((k) => k !== CACHE).map((k) => caches.delete(k))))
  );
  self.clients.claim();
});

async function store(key, response) {
  const cache = await caches.open(CACHE);
  await cache.put(key, response);
}

self.addEventListener('fetch', (event) => {
  const url = new URL(event.request.url);
  // Fremde Adressen (Wiktionary, PeerJS) und alles außer GET erledigt der Browser selbst
  if (event.request.method !== 'GET' || url.origin !== self.location.origin) return;

  // Wortliste: aus dem Speicher, beim ersten Mal aus dem Netz
  if (url.pathname.endsWith(WORDS)) {
    event.respondWith(caches.match(event.request).then((cached) => cached || fetch(event.request).then((res) => {
      if (res.ok) store(event.request, res.clone());
      return res;
    })));
    return;
  }

  // Alles andere: zuerst aus dem Netz, damit immer die aktuelle Version läuft (kein "zweimal neu
  // laden" mehr); nur ohne Verbindung aus dem Speicher. Seitenaufrufe mit Einladungslink
  // (?watch=…) gelten dabei als dieselbe Seite.
  const isPage = event.request.mode === 'navigate';
  const key = isPage ? new URL('./', self.registration.scope).href : event.request;
  event.respondWith(
    fetch(url.href, { cache: 'no-cache', credentials: 'same-origin' })
      .then((res) => {
        if (res.ok) store(key, res.clone());
        return res;
      })
      .catch(() => caches.match(key).then((cached) => cached || Response.error()))
  );
});
