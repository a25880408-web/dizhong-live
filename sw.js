/* 離線快取：打開過一次之後，沒網路也能打開。
 * 0.2.2 起：有網路就先拿線上最新版（跳過手機的 10 分鐘暫存），3 秒內拿不到或沒網路，才用手機裡存的那份。
 * （0.2 的做法是先用手機裡那份、背景抓新版，但背景那次常拿到手機暫存的舊檔，結果一直更新不了。） */
var CACHE = "dizhong";
var FILES = ["./", "./index.html", "./engine.js", "./sample.js", "./manifest.webmanifest",
             "./icon-180.png", "./icon-192.png", "./icon-512.png"];
var WAIT_MS = 3000;

self.addEventListener("install", function (e) {
  e.waitUntil(caches.open(CACHE).then(function (c) {
    return Promise.all(FILES.map(function (u) {
      return fetch(new Request(u, { cache: "reload" })).then(function (res) { if (res.ok) return c.put(u, res); });
    }));
  }).then(function () { return self.skipWaiting(); }));
});
self.addEventListener("activate", function (e) {
  e.waitUntil(caches.keys().then(function (ks) {
    return Promise.all(ks.filter(function (k) { return k !== CACHE; }).map(function (k) { return caches.delete(k); }));
  }).then(function () { return self.clients.claim(); }));
});
self.addEventListener("fetch", function (e) {
  var req = e.request, url = new URL(req.url);
  if (req.method !== "GET" || url.origin !== self.location.origin || req.headers.has("range")) return;
  if (url.searchParams.has("t")) return;   /* 「更新到最新版」按鈕自己抓檔，不經過這裡 */
  e.respondWith(caches.open(CACHE).then(function (c) {
    var fromCache = function () {
      return c.match(req, { ignoreSearch: true }).then(function (hit) {
        return hit || (req.mode === "navigate" ? c.match("./index.html") : null);
      });
    };
    var net = fetch(req, { cache: "no-cache" }).then(function (res) {
      if (res && res.ok) {
        var copy = res.clone();
        c.put(url.pathname.endsWith("/") ? "./" : req, copy.clone());
        if (url.pathname.endsWith("/")) c.put("./index.html", copy);
      }
      return res;
    });
    var timer = new Promise(function (resolve) { setTimeout(function () { resolve(null); }, WAIT_MS); });
    return Promise.race([net.catch(function () { return null; }), timer]).then(function (res) {
      if (res && res.ok) return res;
      return fromCache().then(function (hit) {
        if (hit) return hit;
        return net.catch(function () { return Response.error(); });   /* 手機裡也沒有：再等網路 */
      });
    });
  }));
});
