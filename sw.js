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

// Erst im Speicher suchen; was nachgeladen wird (z. B. das Wörterbuch), wird mitgespeichert
self.addEventListener('fetch', (event) => {
  if (event.request.method !== 'GET') return;
  event.respondWith(
    caches.match(event.request).then((cached) => cached || fetch(event.request).then((res) => {
      if (res.ok && new URL(event.request.url).origin === self.location.origin) {
        const copy = res.clone();
        caches.open(CACHE).then((cache) => cache.put(event.request, copy));
      }
      return res;
    }))
  );
});
