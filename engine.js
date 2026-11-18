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
  function f0At(x, SR, from, loHz, hiHz, maxAp) {
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
      if (mn > (maxAp != null ? maxAp : 0.55)) return 0;   /* 週期性太弱（雜音）就不算 */
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
  function tempoScores(s0, len, bpms, fps, rec) {
    var i, mean = 0;
    for (i = 0; i < len; i++) mean += s0[i];
    mean /= len;
    var s = new Float32Array(len);
    for (i = 0; i < len; i++) s[i] = s0[i] - mean;
    /* 越近的權重越大（rec＝0.8：最舊的 0.2、最新的 1），速度的估計比較貼近「現在」 */
    if (rec) for (i = 0; i < len; i++) s[i] *= Math.sqrt((1 - rec) + rec * (i + 1) / len);
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
      tempoWin: opt.tempoWin || 6,         /* 速度最多用最近幾秒來算（慢的時候用滿） */
      tempoBeats: opt.tempoBeats != null ? opt.tempoBeats : 12,   /* 速度穩了以後只看最近幾下（快的時候窗口變短、比較跟得上）；0＝固定 tempoWin */
      tempoWinMin: opt.tempoWinMin || 3,   /* 窗口最短幾秒 */
      recency: opt.recency != null ? opt.recency : 0.8,   /* 窗口裡越近的敲擊權重越大（0＝一樣重） */
      smooth: opt.smooth != null ? opt.smooth : 1,        /* 顯示值的平滑（1＝不平滑；0.4 前是 0.5） */
      tempoEvery: opt.tempoEvery || 0.25,  /* 幾秒更新一次速度（0.4 前是 0.5） */
      /* 速度變化的代價：3.3 的值是以每 0.5 秒更新一次訂的，更新得更勤就按比例縮小，每秒能變多少不變 */
      costA: opt.costA != null ? opt.costA : 3,      /* 速度變化的代價（每八度） */
      costB: opt.costB != null ? opt.costB : 30,     /* 跳太多（超過 costT 八度）的額外代價 */
      costT: opt.costT != null ? opt.costT : 0.04,
      minConf: opt.minConf != null ? opt.minConf : 0.05, /* 節奏明確度低於這個就不更新（安靜、只有人聲） */
      minLevel: opt.minLevel != null ? opt.minLevel : -60,   /* 高頻音量低於這個（dBFS）當作沒在敲 */
      /* 停了的判斷（0.4）：每次算出的速度要跟追蹤的速度對得上（含兩倍、一半、1.5 倍，差 agreeTol 八度內），
       * 而且沒有突然跳超過 jumpOct 八度，才算「清楚的一次」；超過 stopBeats 下（至少 stopMin 秒）都沒有就算停了 */
      agreeTol: opt.agreeTol != null ? opt.agreeTol : 0.1,
      jumpOct: opt.jumpOct != null ? opt.jumpOct : 0.15,   /* 約 11%：地鐘每秒最多快約 3%，一下子跳這麼多是收尾滾奏或雜音 */
      jumpHold: opt.jumpHold != null ? opt.jumpHold : 5,   /* 跳過去以後持續幾秒才接受（收尾滾奏後的餘音約 3～4 秒） */
      rampOct: opt.rampOct != null ? opt.rampOct : 0.06,  /* 數字停住沒更新時，每過一秒允許多快多少（八度；約 4%，地鐘加速最快約每秒 3%） */
      stopAfter: opt.stopAfter != null ? opt.stopAfter : 20,  /* 開始顯示後至少幾秒才判斷停了（剛開始的慢板節奏本來就不清楚） */
      stopBeats: opt.stopBeats != null ? opt.stopBeats : 12,
      stopMin: opt.stopMin != null ? opt.stopMin : 4,
      resumeFrac: opt.resumeFrac != null ? opt.resumeFrac : 0.85,   /* 停了以後：最近 6 秒清楚的比例要這麼高 */
      resumeSec: opt.resumeSec != null ? opt.resumeSec : 3,         /* 而且持續幾秒，才恢復顯示（講話、雜音不會） */
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
    var rawRing = new Float32Array(K), osfRing = new Float32Array(K), lvRing = new Float32Array(K), nFrames = 0, runSum = 0;
    var onsetMeanSum = 0, ONW = Math.round(FPS * 1.5);
    var lastOnsetT = -1, onsetCount = 0;

    /* 速度格點與 Viterbi */
    var M = 240, BPMS = new Float32Array(M), LSTEP = Math.log(480 / 45) / Math.LN2 / (M - 1);
    for (i = 0; i < M; i++) BPMS[i] = 45 * Math.pow(2, i * LSTEP);
    var TCOST = new Float32Array(M), CS = P.tempoEvery / 0.5;
    for (i = 0; i < M; i++) { var d = i * LSTEP; TCOST[i] = CS * (P.costA * d + P.costB * Math.max(0, d - P.costT * CS)); }
    var V = null, NV = new Float32Array(M), nUpd = 0, framesSinceTempo = 0;
    var tempoIdx = -1, tempoConf = 0, tempoPeak = 0, tempoLevel = -200, lastGoodTempoT = -1e9, bpmSmooth = 0;
    var mult = 1, lastOut = 0;                      /* 只聽得到每兩拍一次的鐘聲時會算成一半 → 接回連續（同 3.3 healOctaves） */
    var obsBest = -1, jumpSince = -1, jumpRef = 0, dispT = -1e9, dispMult = 1;  /* 這一次單獨看的最高點、突然跳的起點和跳到的值 */
    var beatOn = true, lastBeatT = -1e9, stopBpm = null, resumeSince = -1, onSince = -1;
    var GH = Math.round(6 / P.tempoEvery), gHist = new Uint8Array(GH), gN = 0;
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
      /* 這一格最後 HOP 點的高頻音量（一階差分壓掉冷氣、嗡聲這類低頻） */
      var lv = 0, i0 = dcount - HOP;
      for (k = 0; k < HOP; k++) { var dx = dring[(i0 + k) % N] - dring[(i0 + k - 1 + N) % N]; lv += dx * dx; }
      lvRing[f % K] = Math.sqrt(lv / HOP);
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
      var upSec = nUpd * P.tempoEvery;              /* 這一輪已經穩定算了幾秒 */
      /* 窗口：剛開始、慢的時候用滿 6 秒（拍子少，短了會算成兩倍）；穩了以後只看最近 12 下，
       * 例如 240 下／分只看 3 秒，畫面比較跟得上加速。越近的敲擊權重也越大。 */
      var win = P.tempoWin, settled = upSec > 10 && lastOut > 0;
      if (settled && P.tempoBeats) win = Math.max(P.tempoWinMin, Math.min(P.tempoWin, P.tempoBeats * 60 / (lastOut / mult)));
      var len = Math.min(nFrames, Math.round(win * FPS), K), k;
      for (k = 0; k < len; k++) seg[k] = osfRing[(nFrames - len + k) % K];
      var sc = tempoScores(seg, len, BPMS, FPS, settled ? P.recency : 0);
      var t = nFrames * HOP / TSR;
      /* 敲擊有多「尖」：最近幾秒起音曲線的高點（95 百分位）比平均高幾倍。雜音、只有人聲時很低 */
      var srt = Array.prototype.slice.call(seg, 0, len).sort(function (a, b) { return a - b; }), mean0 = 0;
      for (k = 0; k < len; k++) mean0 += seg[k];
      mean0 /= len;
      tempoPeak = mean0 > 0 ? srt[Math.floor(len * 0.95)] / mean0 : 0;
      var lvs = [];
      for (k = 0; k < len; k++) lvs.push(lvRing[(nFrames - len + k) % K]);
      lvs.sort(function (a, b) { return a - b; });
      tempoLevel = 20 * Math.log(lvs[Math.floor(len * 0.95)] + 1e-12) / Math.LN10;
      obsBest = -1;
      if (sc) { obsBest = 0; for (k = 1; k < M; k++) if (sc.s[k] > sc.s[obsBest]) obsBest = k; }
      /* 太小聲（安靜的房間，只有冷氣、電器聲）或節奏不明確：不更新速度 */
      if (!sc || sc.conf < P.minConf || tempoLevel < P.minLevel) { tempoConf = sc ? sc.conf : 0; judgeBeat(t, false, nUpd * P.tempoEvery); return; }
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
        var w = Math.min(1, 0.15 + upSec / 6);
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
      if (lastOut && upSec > 10) {
        var dd = Math.log(b * mult / lastOut) / Math.LN2;
        if (Math.abs(dd) > 0.6) {
          var nm = mult * Math.pow(2, -Math.round(dd));
          if (nm >= 0.25 && nm <= 4) mult = nm;
        }
      }
      b *= mult;
      lastOut = b;
      /* 以上是追速度本身（同 0.3.1）。以下只管畫面：
       * 這一次單獨看的最高點跟追蹤的對得上（含兩倍、一半、1.5 倍），才算「清楚的一次」，拿來判斷停了沒。
       * 畫面上的數字另外要求：不是貼著上限 480（收尾滾奏），也沒有突然跳（跳過去持續 jumpHold 秒才接受） */
      var dOct = obsBest >= 0 ? Math.abs(obsBest - bi) * LSTEP : 9;
      var agree = Math.min(dOct, Math.abs(dOct - 1), Math.abs(dOct - 0.585)) < P.agreeTol;
      /* 地鐘只會越敲越快：數字停住幾秒後，往上可以多跳一點（每秒 rampOct）；往下一次掉超過門檻就是收尾或雜音 */
      var jump = bpmSmooth > 0 && upSec > 10 &&
        Math.abs(Math.log(b / bpmSmooth) / Math.LN2) > P.jumpOct + (b > bpmSmooth ? P.rampOct * Math.max(0, t - dispT) : 0);
      /* 跳過去的值要穩定才累計（480 → 300 → 400 這樣一直換不算） */
      if (jump) {
        if (jumpSince < 0 || Math.abs(Math.log(b / jumpRef) / Math.LN2) > P.jumpOct / 2 + P.rampOct * (t - jumpSince)) { jumpSince = t; jumpRef = b; }
      } else jumpSince = -1;
      judgeBeat(t, agree, upSec);
      if (agree && beatOn && bi < M - 3 && (!jump || t - jumpSince >= P.jumpHold)) {
        bpmSmooth = bpmSmooth ? bpmSmooth + (b - bpmSmooth) * P.smooth : b;
        dispT = t; dispMult = mult;
      }
    }

    /* 有沒有在敲：顯示中超過 stopBeats 下（至少 stopMin 秒）沒有清楚的一次 → 停了（畫面停在最後的速度）；
     * 停了以後要最近 6 秒九成左右都清楚、持續 resumeSec 秒才恢復，講話、雜音不會讓數字又跑出來 */
    function judgeBeat(t, good, upSec) {
      gHist[gN % GH] = good ? 1 : 0; gN++;
      if (good) lastBeatT = t;
      if (beatOn) {
        var ref = bpmSmooth > 0 ? bpmSmooth : lastOut, per = ref > 0 ? 60 / ref : 0.2;   /* 用畫面上的速度（雜音裡接的倍數不算） */
        if (onSince < 0 && upSec > 10) onSince = t;     /* 開始顯示 */
        if (onSince >= 0 && t - onSince >= P.stopAfter && lastBeatT > -1e8 && t - lastBeatT > Math.max(P.stopMin, P.stopBeats * per)) {
          beatOn = false; resumeSince = -1; onSince = -1;
          stopBpm = bpmSmooth > 0 ? bpmSmooth : null;
          V = null; nUpd = 0; mult = 1; lastOut = 0; bpmSmooth = 0; jumpSince = -1; dispMult = 1;   /* 重新開始時從頭抓 */
        }
      } else {
        var s = 0;
        for (var q = 0; q < GH; q++) s += gHist[q];
        if (gN >= GH && s / GH >= P.resumeFrac) {
          if (resumeSince < 0) resumeSince = t;
          if (t - resumeSince >= P.resumeSec) {           /* 恢復：停了那段雜音裡接的倍數不算 */
            beatOn = true; resumeSince = -1; onSince = t; mult = 1; lastOut = tempoIdx >= 0 ? BPMS[tempoIdx] : 0;
          }
        } else resumeSince = -1;
      }
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
      /* 即時版比 3.3 嚴格：週期性要夠明顯，也不收貼著上下限的值（低頻雜音常被量成剛好 70 Hz） */
      var f = f0At(ptmp, SR, 0, 70, 520, 0.3);
      if (f > 74 && f < 500) pts.push({ t: t, m: toMidi(f) });
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
      var live = beatOn && bpmSmooth > 0 && tempoIdx >= 0 && nUpd * P.tempoEvery >= 10 && t - lastGoodTempoT < 4;   /* 剛開始 10 秒的估計還在跳，不顯示 */
      /* 開頭取樣：先收 4 秒聲音才算第一次，再算滿 10 秒（節奏夠清楚的那幾次才算）才顯示。給畫面倒數用 */
      var warm = null;
      if (beatOn && (nUpd * P.tempoEvery < 10 || bpmSmooth <= 0)) {
        var left = Math.max(0, 4 - nFrames / FPS) + Math.max(0, 10 - nUpd * P.tempoEvery);
        warm = { left: left, frac: Math.max(0, Math.min(1, 1 - left / 14)),
                 stalled: nFrames >= FPS * 4 && t - lastGoodTempoT > 1.5 };   /* 沒聽到清楚的木魚聲：倒數停住 */
      }
      return {
        t: t,
        bpm: live ? bpmSmooth : null,
        stopped: !beatOn,                 /* 判斷成停了（地鐘結束、只剩講話或雜音） */
        lastBpm: beatOn ? null : stopBpm, /* 停之前最後的速度 */
        tempoConf: tempoConf,
        tempoPeak: tempoPeak,
        tempoLevel: tempoLevel,           /* 最近幾秒高頻音量的高點（dBFS） */
        autoMult: dispMult,              /* 1 以外＝自動接回過倍數（畫面上那個數字用的） */
        lastOnsetAgo: lastOnsetT >= 0 ? t - lastOnsetT : null,
        onsets: onsetCount,
        note: cachedPitch.note,          /* 現在唱的音（半音刻度，可帶小數） */
        key: cachedPitch.key,            /* 現在的調：四字佛號「阿」的音 */
        keyN: cachedPitch.keyN,
        keyFrac: cachedPitch.key != null ? 1 : Math.min(1, cachedPitch.keyN / 30),   /* 調的取樣進度（唱得穩的點要 30 個） */
        warm: warm                        /* 速度還在取樣：{ left 剩幾秒, frac 進度, stalled 等木魚聲 }，其他時候 null */
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
    api.rearm = function () { if (!beatOn) { beatOn = true; lastBeatT = -1e9; resumeSince = -1; onSince = -1; } };   /* 使用者重新按開始：照第一次那樣抓 */
    api.sampleRate = SR;
    return api;
  }

  var DZ = { createEngine: createEngine, noteOf: noteOf, toMidi: toMidi, midiToHz: midiToHz, NOTE_NAMES: NOTE_NAMES };
  if (typeof module !== "undefined" && module.exports) module.exports = DZ;
  else root.DZ = DZ;
})(typeof self !== "undefined" ? self : this);
