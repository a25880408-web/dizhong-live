/* 地鐘即時分析引擎（速度＋唱誦音高）
 * 只做計算、不碰畫面：手機網頁（index.html）和電腦上的比對測試（test/compare.js）共用這一份。
 * 演算法沿用「地鐘節拍器 3.3」的離線分析，改成邊聽邊算：
 *   速度：法器聲頻帶（400–5000 Hz）的頻譜差分 → 最近幾秒做自相關＋梳狀加權 → 只往前看的 Viterbi（速度要連續）
 *   音高：YIN 量基頻 → 男女眾折回同一個八度 → 最近 20 秒裡「最低的常唱音」＝四字佛號的「阿」＝現在的調
 * 用法：var eng = DZ.createEngine({sampleRate: 48000}); eng.push(Float32Array 單聲道); eng.state();
 */
(function (root) {
  "use strict";

  var NOTE_NAMES = ["C", "#C", "D", "#D", "E", "F", "#F", "G", "#G", "A", "#A", "B"];
  function toMidi(hz) { return 12 * Math.log(hz / 440) / Math.LN2 + 69; }
  function midiToHz(m) { return 440 * Math.pow(2, (m - 69) / 12); }
  function noteOf(m) {
    var r = Math.round(m);
    return { name: NOTE_NAMES[((r % 12) + 12) % 12] + (Math.floor(r / 12) - 1),
             cents: Math.round((m - r) * 100), midi: r };
  }
  function num(a, b) { return a - b; }
  function medianOf(a) {
    if (!a.length) return 0;
    var s = a.slice().sort(num);
    return s[s.length >> 1];
  }

  /* ---------- YIN 風格的基頻偵測（人聲用，同 3.3） ---------- */
  function f0At(x, SR, from, loHz, hiHz) {
    var W = Math.round(SR / loHz) * 2;
    if (from + W * 2 > x.length) return 0;
    var tauMin = Math.floor(SR / hiHz), tauMax = Math.min(Math.floor(SR / loHz), W);
    var d = new Float32Array(tauMax + 1), cum = new Float32Array(tauMax + 1), tau, i;
    for (tau = tauMin; tau <= tauMax; tau++) {
      var s = 0;
      for (i = 0; i < W; i++) { var diff = x[from + i] - x[from + i + tau]; s += diff * diff; }
      d[tau] = s;
    }
    var run = 0;
    for (tau = tauMin; tau <= tauMax; tau++) {
      run += d[tau];
      cum[tau] = d[tau] * (tau - tauMin + 1) / (run || 1e-9);
    }
    var best = -1;
    for (tau = tauMin + 1; tau < tauMax; tau++) {
      if (cum[tau] < 0.2 && cum[tau] <= cum[tau + 1]) { best = tau; break; }
    }
    if (best < 0) {
      var mn = 1e9;
      for (tau = tauMin + 1; tau < tauMax; tau++) if (cum[tau] < mn) { mn = cum[tau]; best = tau; }
      if (mn > 0.55) return 0;
    }
    var a = d[best - 1], b = d[best], c = d[best + 1];
    var shift = (a - c) / (2 * (a - 2 * b + c) || 1e-9);
    return SR / (best + Math.max(-1, Math.min(1, shift)));
  }

  /* ---------- 極簡 FFT（就地、長度 2 的次方，同 3.3） ---------- */
  function fft(re, im) {
    var n = re.length, i, j = 0, k, m, t;
    for (i = 1; i < n; i++) {
      var bit = n >> 1;
      for (; j & bit; bit >>= 1) j ^= bit;
      j ^= bit;
      if (i < j) { t = re[i]; re[i] = re[j]; re[j] = t; t = im[i]; im[i] = im[j]; im[j] = t; }
    }
    for (m = 2; m <= n; m <<= 1) {
      var ang = -2 * Math.PI / m, wr = Math.cos(ang), wi = Math.sin(ang);
      for (i = 0; i < n; i += m) {
        var cr = 1, ci = 0;
        for (k = 0; k < m / 2; k++) {
          var xr = re[i + k], xi = im[i + k];
          var yr = re[i + k + m / 2] * cr - im[i + k + m / 2] * ci;
          var yi = re[i + k + m / 2] * ci + im[i + k + m / 2] * cr;
          re[i + k] = xr + yr; im[i + k] = xi + yi;
          re[i + k + m / 2] = xr - yr; im[i + k + m / 2] = xi - yi;
          var ncr = cr * wr - ci * wi; ci = cr * wi + ci * wr; cr = ncr;
        }
      }
    }
  }

  /* 一段時間窗的速度分數（自相關＋梳狀加權，同 3.3），另外回傳「節奏有多明確」 */
  function tempoScores(s0, len, bpms, fps) {
    var i, mean = 0;
    for (i = 0; i < len; i++) mean += s0[i];
    mean /= len;
    var s = new Float32Array(len);
    for (i = 0; i < len; i++) s[i] = s0[i] - mean;
    var maxLag = Math.min(len - 1, Math.round(2.6 * fps));
    var ac = new Float32Array(maxLag + 1);
    for (var L = 0; L <= maxLag; L++) {
      var sum = 0;
      for (i = 0; i + L < len; i++) sum += s[i] * s[i + L];
      ac[L] = sum;
    }
    if (ac[0] <= 0) return null;
    var a0 = ac[0];                                 /* 3.3 原本邊除邊改 ac[0]，只有 ac[0] 被正規化；排名不受影響，但明確度要用真的比值 */
    for (L = 0; L <= maxLag; L++) ac[L] /= a0;
    var val = function (sec) {
      var p = sec * fps, i0 = Math.floor(p), w = p - i0;
      if (i0 < 0 || i0 + 1 > maxLag) return 0;
      var v = ac[i0] * (1 - w) + ac[i0 + 1] * w;
      return v > 0 ? v : 0;
    };
    var out = new Float32Array(bpms.length), mx = 0, peak = 0;
    for (i = 0; i < bpms.length; i++) {
      var lag = 60 / bpms[i];
      var v1 = val(lag);
      var v = v1 + 0.8 * val(2 * lag) + 0.6 * val(3 * lag) + 0.4 * val(4 * lag)
            - 1.4 * Math.max(val(lag / 2), val(lag / 3));
      out[i] = v > 0 ? v : 0;
      if (out[i] > mx) { mx = out[i]; peak = v1; }
    }
    if (mx > 0) for (i = 0; i < bpms.length; i++) out[i] /= mx;
    return { s: out, conf: peak };
  }

  /* 直方圖找最常出現的音（半音刻度，同 3.3） */
  function histPeak(vals, from, to) {
    var B = 0.25, n = Math.ceil((to - from) / B) + 1, h = new Float64Array(n), i;
    for (i = 0; i < vals.length; i++) {
      var k = Math.round((vals[i] - from) / B);
      if (k >= 0 && k < n) { h[k] += 1; if (k > 0) h[k - 1] += 0.5; if (k < n - 1) h[k + 1] += 0.5; }
    }
    var best = 0, bi = 0;
    for (i = 0; i < n; i++) if (h[i] > best) { best = h[i]; bi = i; }
    return { mid: from + bi * B, h: h, B: B, max: best };
  }
  /* 一段唱誦裡最低的那個常唱音 —— 四字佛號的「阿」（同 3.3 lowBand，輸入輸出都是半音刻度） */
  function lowBand(ms) {
    if (ms.length < 20) return null;
    var srt = ms.slice().sort(num);
    var lo = Math.floor(srt[0]) - 1, hi = Math.ceil(srt[srt.length - 1]) + 1;
    var H = histPeak(ms, lo, hi), i, best = -1, need = ms.length * 0.12;
    for (i = 1; i < H.h.length - 1; i++) {
      if (!(H.h[i] >= H.h[i - 1] && H.h[i] > H.h[i + 1] && H.h[i] > 0.35 * H.max)) continue;
      var cm0 = lo + i * H.B, mass = 0, k;
      for (k = 0; k < ms.length; k++) if (Math.abs(ms[k] - cm0) < 0.6) mass++;
      if (mass >= need) { best = i; break; }
    }
    if (best < 0) return medianOf(ms);
    var cm = lo + best * H.B;
    return medianOf(ms.filter(function (v) { return Math.abs(v - cm) < 0.5; }));
  }

  /* 二階高通（去掉冷氣、腳步的低頻） */
  function makeHighpass(fc, SR) {
    var w0 = 2 * Math.PI * fc / SR, cw = Math.cos(w0), al = Math.sin(w0) / (2 * Math.SQRT1_2);
    var a0 = 1 + al, b0 = (1 + cw) / 2 / a0, b1 = -(1 + cw) / a0, b2 = b0, a1 = -2 * cw / a0, a2 = (1 - al) / a0;
    var x1 = 0, x2 = 0, y1 = 0, y2 = 0;
    return function (x) {
      var y = b0 * x + b1 * x1 + b2 * x2 - a1 * y1 - a2 * y2;
      x2 = x1; x1 = x; y2 = y1; y1 = y;
      return y;
    };
  }

  function createEngine(opt) {
    opt = opt || {};
    var SR = opt.sampleRate || 48000;
    var api = {};
    var P = {
      tempoWin: opt.tempoWin || 6,         /* 速度用最近幾秒來算 */
      tempoEvery: opt.tempoEvery || 0.5,   /* 幾秒更新一次速度 */
      costA: opt.costA != null ? opt.costA : 3,      /* 速度變化的代價（每八度） */
      costB: opt.costB != null ? opt.costB : 30,     /* 跳太多（超過 costT 八度）的額外代價 */
      costT: opt.costT != null ? opt.costT : 0.04,
      minConf: opt.minConf != null ? opt.minConf : 0.05, /* 節奏明確度低於這個就不更新（安靜、只有人聲） */
      keyWin: opt.keyWin || 20             /* 「現在的調」看最近幾秒 */
    };

    /* ---------- 速度前端：降到約 11 kHz，STFT 頻譜差分 ---------- */
    var D = Math.max(1, Math.round(SR / 11025)), TSR = SR / D;
    var N = 1024, HOP = 128, FPS = TSR / HOP;
    var BLO = Math.max(1, Math.floor(400 / TSR * N)), BHI = Math.min(N / 2, Math.ceil(5000 / TSR * N));
    var hann = new Float32Array(N), i;
    for (i = 0; i < N; i++) hann[i] = 0.5 - 0.5 * Math.cos(2 * Math.PI * i / N);
    var dring = new Float32Array(N), dcount = 0, decAcc = 0, decN = 0, sinceHop = 0;
    var re = new Float32Array(N), im = new Float32Array(N);
    var prevMag = new Float32Array(BHI - BLO), curMag = new Float32Array(BHI - BLO);
    var DET = 150;                                  /* 去掉緩慢起伏用的平均長度（約 1.6 秒） */
    var K = Math.ceil(FPS * 30);                    /* 保留 30 秒的起音曲線 */
    var rawRing = new Float32Array(K), osfRing = new Float32Array(K), nFrames = 0, runSum = 0;
    var onsetMeanSum = 0, ONW = Math.round(FPS * 1.5);
    var lastOnsetT = -1, onsetCount = 0;

    /* 速度格點與 Viterbi */
    var M = 240, BPMS = new Float32Array(M), LSTEP = Math.log(480 / 45) / Math.LN2 / (M - 1);
    for (i = 0; i < M; i++) BPMS[i] = 45 * Math.pow(2, i * LSTEP);
    var TCOST = new Float32Array(M);
    for (i = 0; i < M; i++) { var d = i * LSTEP; TCOST[i] = P.costA * d + P.costB * Math.max(0, d - P.costT); }
    var V = null, NV = new Float32Array(M), nUpd = 0, framesSinceTempo = 0;
    var tempoIdx = -1, tempoConf = 0, lastGoodTempoT = -1e9, bpmSmooth = 0;
    var mult = 1, lastOut = 0;                      /* 只聽得到每兩拍一次的鐘聲時會算成一半 → 接回連續（同 3.3 healOctaves） */
    var TEMPO_EVERY_F = Math.max(1, Math.round(P.tempoEvery * FPS));
    var seg = new Float32Array(Math.ceil(P.tempoWin * FPS) + 2);

    /* ---------- 音高前端 ---------- */
    var hp = makeHighpass(70, SR);
    var PW = Math.round(SR / 70) * 2, PLEN = PW * 2 + 4;
    var PR = 1; while (PR < PLEN * 2) PR <<= 1;
    var pring = new Float32Array(PR), pcount = 0;
    var ptmp = new Float32Array(PLEN);
    var ENV_HOP = Math.round(SR * 0.01), ENV_WIN = Math.round(SR * 0.03), sinceEnv = 0, envTick = 0;
    var ENV_KEEP = 3000, envRing = new Float32Array(ENV_KEEP), envN = 0, envThr = 0;
    var pts = [];                                   /* {t, m}：量到的音（半音刻度） */
    var history = [], lastHistT = -1;

    function now() { return (pcount) / SR; }

    function onTempoFrame() {
      /* 一個 STFT 影格 */
      var start = dcount - N, k;
      for (k = 0; k < N; k++) { re[k] = dring[(start + k) % N] * hann[k]; im[k] = 0; }
      fft(re, im);
      var acc = 0;
      for (k = BLO; k < BHI; k++) {
        var mag = Math.log(1 + 20 * Math.sqrt(re[k] * re[k] + im[k] * im[k]));
        curMag[k - BLO] = mag;
        var dd = mag - prevMag[k - BLO];
        if (dd > 0) acc += dd;
      }
      var tmp = prevMag; prevMag = curMag; curMag = tmp;
      var f = nFrames;
      if (f === 0) acc = 0;                         /* 第一格沒有前一格可比 */
      rawRing[f % K] = acc; runSum += acc;
      if (f >= DET) runSum -= rawRing[(f - DET) % K];
      var o = Math.max(0, acc - runSum / Math.min(f + 1, DET));
      osfRing[f % K] = o;
      onsetMeanSum += o;
      if (f >= ONW) onsetMeanSum -= osfRing[(f - ONW) % K];
      nFrames++;

      /* 起音事件（晚 2 格判斷是不是局部最高），給畫面閃燈、音高避開敲擊瞬間用 */
      if (nFrames > 5) {
        var c = osfRing[(nFrames - 3) % K], isMax = true;
        for (k = 1; k <= 5; k++) if (k !== 3 && osfRing[(nFrames - k) % K] > c) { isMax = false; break; }
        var mean = onsetMeanSum / Math.min(nFrames, ONW);
        var tOn = (nFrames - 3) * HOP / TSR + N / TSR / 2;
        if (isMax && c > 2.2 * mean + 1e-6 && tOn - lastOnsetT > 0.12) { lastOnsetT = tOn; onsetCount++; }
      }

      framesSinceTempo++;
      if (framesSinceTempo >= TEMPO_EVERY_F && nFrames >= FPS * 4) {
        framesSinceTempo = 0;
        updateTempo();
      }
    }

    function updateTempo() {
      var len = Math.min(nFrames, Math.round(P.tempoWin * FPS), K), k;
      for (k = 0; k < len; k++) seg[k] = osfRing[(nFrames - len + k) % K];
      var sc = tempoScores(seg, len, BPMS, FPS);
      var t = nFrames * HOP / TSR;
      if (!sc || sc.conf < P.minConf) { tempoConf = sc ? sc.conf : 0; return; }
      tempoConf = sc.conf;
      if (lastGoodTempoT > 0 && t - lastGoodTempoT > 6) {   /* 停了一陣子再開始：重新抓 */
        V = null; nUpd = 0; mult = 1; lastOut = 0; bpmSmooth = 0;
      }
      var obs = sc.s, j, p;
      if (!V) {
        V = new Float32Array(M);
        for (j = 0; j < M; j++) V[j] = obs[j];
      } else {
        /* 剛開始幾次放寬連續性，讓它先找到對的八度 */
        var w = Math.min(1, 0.15 + nUpd / 12);
        var mx = -1e9;
        for (j = 0; j < M; j++) {
          var best = -1e9;
          var p0 = Math.max(0, j - 80), p1 = Math.min(M - 1, j + 80);
          for (p = p0; p <= p1; p++) {
            var cst = V[p] - w * TCOST[p > j ? p - j : j - p];
            if (cst > best) best = cst;
          }
          if (p0 > 0 || p1 < M - 1) {                /* 遠的格點：只看端點以外的最大值＋最大代價 */
            var far = -1e9;
            for (p = 0; p < p0; p++) if (V[p] > far) far = V[p];
            for (p = p1 + 1; p < M; p++) if (V[p] > far) far = V[p];
            far -= w * TCOST[80];
            if (far > best) best = far;
          }
          NV[j] = best + obs[j];
          if (NV[j] > mx) mx = NV[j];
        }
        for (j = 0; j < M; j++) V[j] = NV[j] - mx;
      }
      nUpd++;
      var bi = 0;
      for (j = 1; j < M; j++) if (V[j] > V[bi]) bi = j;
      tempoIdx = bi;
      lastGoodTempoT = t;
      var b = BPMS[bi];
      /* 拋物線內插讓數字細一點 */
      if (bi > 0 && bi < M - 1) {
        var a0 = V[bi - 1], b0 = V[bi], c0 = V[bi + 1], den = a0 - 2 * b0 + c0;
        if (den < 0) b = 45 * Math.pow(2, (bi + Math.max(-0.5, Math.min(0.5, 0.5 * (a0 - c0) / den))) * LSTEP);
      }
      /* 地鐘只會越敲越快，突然變一半或兩倍不是真的。剛開始 10 秒還在找速度，不接 */
      if (lastOut && nUpd > 20) {
        var dd = Math.log(b * mult / lastOut) / Math.LN2;
        if (Math.abs(dd) > 0.6) {
          var nm = mult * Math.pow(2, -Math.round(dd));
          if (nm >= 0.25 && nm <= 4) mult = nm;
        }
      }
      b *= mult;
      lastOut = b;
      bpmSmooth = bpmSmooth ? bpmSmooth + (b - bpmSmooth) * 0.5 : b;
    }

    function onEnvTick() {
      /* 每 10 毫秒：量最近 30 毫秒的音量 */
      var acc = 0, k, base = pcount - ENV_WIN;
      for (k = 0; k < ENV_WIN; k++) { var v = pring[(base + k) & (PR - 1)]; acc += v * v; }
      var env = Math.sqrt(acc / ENV_WIN);
      envRing[envN % ENV_KEEP] = env; envN++;
      envTick++;
      if (envTick % 100 === 1) {                    /* 每秒重算一次「有在唱」的門檻 */
        var n = Math.min(envN, ENV_KEEP), arr = Array.prototype.slice.call(envRing, 0, n).sort(num);
        envThr = Math.max(1e-4, arr[Math.floor(n * 0.98)] * 0.16);
      }
      if (envTick % 5 !== 0) return;                /* 每 50 毫秒量一次音高 */
      var t = now();
      if (env < envThr) return;
      if (lastOnsetT >= 0 && t - lastOnsetT < 0.05) return;   /* 避開木魚、鐘敲下去那一瞬間 */
      var st = pcount - PLEN;
      for (k = 0; k < PLEN; k++) ptmp[k] = pring[(st + k) & (PR - 1)];
      var f = f0At(ptmp, SR, 0, 70, 520);
      if (f > 70 && f < 520) pts.push({ t: t, m: toMidi(f) });
      if (pts.length > 2000 || (pts.length && t - pts[0].t > 60)) {
        var cut = 0;
        while (cut < pts.length && t - pts[cut].t > 60) cut++;
        if (pts.length - cut > 1500) cut = pts.length - 1500;
        if (cut) pts.splice(0, cut);
      }
    }

    /* 音高統計：折八度 → 去掉不穩的點 → 「現在唱的音」與「現在的調（阿）」 */
    function pitchStats(t) {
      var recent = [], k;
      for (k = 0; k < pts.length; k++) if (t - pts[k].t <= 30) recent.push(pts[k]);
      if (recent.length < 12) return { note: null, key: null, keyN: 0, center: null };
      var c = histPeak(recent.map(function (p) { return p.m; }), 36, 84).mid;
      var fold = recent.map(function (p) {
        var v = p.m;
        while (v < c - 9) v += 12;
        while (v > c + 9) v -= 12;
        return { t: p.t, m: v };
      });
      /* 只留「唱得穩」的點：前後 3 點的中位數相差 45 音分以內 */
      var stable = [];
      for (k = 0; k < fold.length; k++) {
        var a = [];
        for (var q = Math.max(0, k - 3); q <= Math.min(fold.length - 1, k + 3); q++) a.push(fold[q].m);
        var md = medianOf(a);
        if (Math.abs(fold[k].m - md) < 0.45) stable.push(fold[k]);
      }
      var note = null, lastN = [];
      for (k = fold.length - 1; k >= 0 && t - fold[k].t <= 0.4; k--) lastN.push(fold[k].m);
      if (lastN.length >= 2) note = medianOf(lastN);
      var keyPts = stable.filter(function (p) { return t - p.t <= P.keyWin; }).map(function (p) { return p.m; });
      var key = keyPts.length >= 30 ? lowBand(keyPts) : null;
      return { note: note, key: key, keyN: keyPts.length, center: c };
    }

    function push(x) {
      for (var n = 0; n < x.length; n++) {
        var s = x[n];
        /* 速度：降取樣（平均 D 點） */
        decAcc += s; decN++;
        if (decN === D) {
          dring[dcount % N] = decAcc / D; dcount++; decAcc = 0; decN = 0;
          sinceHop++;
          if (sinceHop >= HOP && dcount >= N) { sinceHop = 0; onTempoFrame(); }
        }
        /* 音高：高通後存起來 */
        pring[pcount & (PR - 1)] = hp(s); pcount++;
        sinceEnv++;
        if (sinceEnv >= ENV_HOP && pcount >= PLEN) { sinceEnv = 0; onEnvTick(); }
      }
      var t = now();
      if (t - lastHistT >= 1) {
        lastHistT = t;
        var st = state();
        history.push({ t: Math.round(t), bpm: st.bpm ? Math.round(st.bpm * 10) / 10 : null,
                       key: st.key != null ? Math.round(st.key * 100) / 100 : null });
        if (history.length > 7200) history.shift();
      }
    }

    var cachedPitch = null, cachedAt = -1;
    function state() {
      var t = now();
      if (t - cachedAt >= 0.2 || !cachedPitch) { cachedPitch = pitchStats(t); cachedAt = t; }
      var live = tempoIdx >= 0 && nUpd >= 20 && t - lastGoodTempoT < 4;   /* 剛開始 10 秒的估計還在跳，不顯示 */
      return {
        t: t,
        bpm: live ? bpmSmooth : null,
        tempoConf: tempoConf,
        autoMult: mult,                  /* 1 以外＝自動接回過倍數 */
        lastOnsetAgo: lastOnsetT >= 0 ? t - lastOnsetT : null,
        onsets: onsetCount,
        note: cachedPitch.note,          /* 現在唱的音（半音刻度，可帶小數） */
        key: cachedPitch.key,            /* 現在的調：四字佛號「阿」的音 */
        keyN: cachedPitch.keyN
      };
    }

    function reset() {
      var fresh = createEngine(opt);
      for (var k in fresh) api[k] = fresh[k];
    }

    api.push = push;
    api.state = state;
    api.history = history;
    api.reset = reset;
    api.sampleRate = SR;
    return api;
  }

  var DZ = { createEngine: createEngine, noteOf: noteOf, toMidi: toMidi, midiToHz: midiToHz, NOTE_NAMES: NOTE_NAMES };
  if (typeof module !== "undefined" && module.exports) module.exports = DZ;
  else root.DZ = DZ;
})(typeof self !== "undefined" ? self : this);
