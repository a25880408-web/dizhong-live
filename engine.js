/* 地鐘即時分析引擎（速度＋唱誦音高）
 * 只做計算、不碰畫面：手機網頁（index.html）和電腦上的比對測試（test/compare.js）共用這一份。
 * 演算法沿用「地鐘節拍器 3.3」的離線分析，改成邊聽邊算：
 *   速度：法器聲頻帶（400–5000 Hz）的頻譜差分 → 最近幾秒做自相關＋梳狀加權 → 只往前看的 Viterbi（速度要連續）
 *         開頭慢板另看「強的起音是不是大多落在固定間隔的格子上」（0.6）
 *   音高：YIN 量基頻 → 最近 20 秒唱得穩的點 → 音名圈上找「阿」（下面空、上面有彌和陀佛，0.5 起同「地鐘節拍器 3.5」）＝現在的調
 * 用法：var eng = DZ.createEngine({sampleRate: 48000}); eng.push(Float32Array 單聲道); eng.state(); eng.force()（「地鐘開始了」）
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
  /* 圈上的差（−6～6 半音） */
  function circ(d) { while (d > 6) d -= 12; while (d <= -6) d += 12; return d; }
  /* 一群音（半音刻度）裡「阿」的音名（0～12，可帶小數），回傳 { pc, bands }（bands＝其他常唱音，給接續前一次用）。
   * 0.5 起改用「地鐘節拍器 3.5」的做法（dzAhClass），取代「折回中心上下 9 個半音、取最低的常唱音」（lowBand）：
   *   - 上下 9 個半音同一個音會留在兩個八度，男眾唱的「陀佛」#C3 被當成最低音「阿」；
   *   - 錄音裡常有比「阿」高五度的音（0902 的 E、0922 的 D），折回後會跑到「阿」下面。
   * 做法：音名排成一圈（男女眾差八度自然重疊），每個常唱音打分數＝自己的點數＋上面 5 個半音內（彌、陀佛）－2×下面 4.5 個半音內；
   * 「阿」至少要有最常唱那個音的四成（底下零星的滑音不算）；相距不到 1 個半音的高點併成一個。
   * 只聽得到一個音、上面沒有旋律（例如節拍器的合成聲）就回傳 null。 */
  function ahClass(ms) {
    var n = ms.length, NB = 120, cnt = new Float64Array(NB), sm = new Float64Array(NB), k, j;
    var pcs = ms.map(function (m) { return ((m % 12) + 12) % 12; });
    pcs.forEach(function (p) { cnt[Math.round(p * 10) % NB] += 1; });
    for (k = 0; k < NB; k++) for (j = -5; j <= 5; j++) sm[k] += cnt[(k + j + NB) % NB];
    var mass = function (c, lo, hi) {
      var s = 0;
      pcs.forEach(function (p) { var d = circ(p - c); if (d > lo && d <= hi) s++; });
      return s;
    };
    var cand = [], peaks = [];
    for (k = 0; k < NB; k++) {
      if (sm[k] >= n * 0.06 && sm[k] >= sm[(k + NB - 1) % NB] && sm[k] > sm[(k + 1) % NB]) cand.push({ c: k / 10, s: sm[k] });
    }
    cand.sort(function (a, b) { return b.s - a.s; });
    cand.forEach(function (p) {
      if (!peaks.some(function (q) { return Math.abs(circ(q.c - p.c)) < 1; })) peaks.push(p);
    });
    if (peaks.length < 2) return null;
    var best = null, bs = -1e9;
    peaks.forEach(function (p) {
      if (p.s < peaks[0].s * 0.4) return;
      var sc = mass(p.c, -0.5, 0.5) + mass(p.c, 0.6, 5) - 2 * mass(p.c, -4.5, -0.6);
      if (sc > bs) { bs = sc; best = p.c; }
    });
    if (best == null || mass(best, 0.6, 5) < n * 0.1) return null;
    var fine = function (c) {
      var off = [];
      pcs.forEach(function (p) { var d = circ(p - c); if (Math.abs(d) < 0.5) off.push(d); });
      return (((c + medianOf(off)) % 12) + 12) % 12;
    };
    return { pc: fine(best), bands: peaks.map(function (p) { return fine(p.c); }) };
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
      /* 0.5.1：追蹤剛開始（或從頭抓）的前幾秒放寬連續性，追到的幾乎就是當下的最高點，跟單獨看的「對得上」不代表節奏清楚，不算數 */
      trustSec: opt.trustSec != null ? opt.trustSec : 6,
      /* 0.5.1：還沒顯示（剛開始聽、停了以後）時，連續幾秒都不清楚就從頭抓，免得雜音裡追到的速度、倍數帶進木魚聲（實測會先顯示兩倍 6 秒） */
      resetSec: opt.resetSec != null ? opt.resetSec : 2,
      /* 0.6 慢板格子：開頭每分鐘 60 下左右，6 秒只有 6 下，上面的「對得上」常常不成立。另外看最近 gridWin 秒的起音：
       * 找一組固定間隔的格子，強的起音（最近起音中位數的 gridHit 倍）大多落在格子上、格子外的強起音少（分數＝落在格子上的比例－格子外強起音占的比例），
       * 最近 gridHold 次（每 0.5 秒一次）有 gridFrac 以上分數 ≥ gridScore、速度差 gridTol2 以內，就算慢板木魚聽清楚了。只在 gridMax 下／分以下用 */
      grid: opt.grid != null ? opt.grid : 1,
      gridWin: opt.gridWin || 10,
      gridHit: opt.gridHit != null ? opt.gridHit : 2,
      gridHitOn: opt.gridHitOn != null ? opt.gridHitOn : 1.5,   /* 已經在顯示（只用來判斷還有沒有在敲）時放寬：慢板有時唱誦的起音跟木魚差不多強 */
      gridOff: opt.gridOff != null ? opt.gridOff : 2,
      gridTol: opt.gridTol != null ? opt.gridTol : 0.06,
      gridScore: opt.gridScore != null ? opt.gridScore : 0.3,
      gridHold: opt.gridHold || 12,
      gridFrac: opt.gridFrac != null ? opt.gridFrac : 0.75,
      gridTol2: opt.gridTol2 != null ? opt.gridTol2 : 0.06,
      gridMax: opt.gridMax || 130,
      gridStart: opt.gridStart != null ? opt.gridStart : 3,      /* 格子連續聽清楚幾秒才開始顯示 */
      /* 靠格子開始顯示的，probation 秒內就判斷停了：當作誤判（規律的雜音、別的法器），不留灰色數字，回到等木魚聲 */
      probation: opt.probation != null ? opt.probation : 40,
      /* 0.7 地鐘儀表板（使用者：「只會測地鐘的速度」「不可能超過400」「一開始大約50~60」「中間會慢慢加速，不會跳太快」
       * 「數字可以掉下，就是警示打地鐘的菩薩」）。12 支地鐘錄音（節拍器 3.5 整段分析）：開頭 45～70、最高 163～355、每 10 秒最多快 8～10%。
       * 速度範圍 minBpm～maxBpm。追到的速度、它的兩倍、它的一半，挑最接近「最近 dashTrend 秒畫面數字的中位數」的那個：
       * 一下子跳成兩倍或一半是算錯，換算回來；菩薩真的放慢、加快是一點一點變，中位數跟著走，照實顯示 */
      minBpm: opt.minBpm || 45,         /* 錄音裡地鐘開頭最慢 45；0.7 試過 40，追蹤會停在一半（農禪寺 82 → 41）*/
      maxBpm: opt.maxBpm || 400,
      dashTrend: opt.dashTrend || 10,
      dashReset: opt.dashReset != null ? opt.dashReset : 90,   /* 停了超過這麼多秒再恢復，當作新的一次地鐘，不接著之前的數字 */
      fastStart: opt.fastStart || 130,                          /* 這一份還沒出過數字、速度在這以上（地鐘開頭不會這麼快）要清楚得久一點 */
      fastStartSec: opt.fastStartSec != null ? opt.fastStartSec : 10,
      /* 0.6「地鐘開始了」按鈕：按了以後這麼多秒內不判斷停了 */
      forceHold: opt.forceHold != null ? opt.forceHold : 60,
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
    /* 速度格點：minBpm～maxBpm（0.7 前 45～480），每格寬度不變（約 1%），Viterbi 的代價照舊 */
    var LSTEP = Math.log(480 / 45) / Math.LN2 / 239, BMIN = P.minBpm;
    var M = Math.round(Math.log(P.maxBpm / BMIN) / Math.LN2 / LSTEP) + 1, BPMS = new Float32Array(M);
    for (i = 0; i < M; i++) BPMS[i] = BMIN * Math.pow(2, i * LSTEP);
    var TCOST = new Float32Array(M), CS = P.tempoEvery / 0.5;
    for (i = 0; i < M; i++) { var d = i * LSTEP; TCOST[i] = CS * (P.costA * d + P.costB * Math.max(0, d - P.costT * CS)); }
    var V = null, NV = new Float32Array(M), nUpd = 0, framesSinceTempo = 0;
    var tempoIdx = -1, tempoConf = 0, tempoPeak = 0, tempoLevel = -200, lastGoodTempoT = -1e9, bpmSmooth = 0;
    var mult = 1, lastOut = 0;                      /* 只聽得到每兩拍一次的鐘聲時會算成一半 → 接回連續（同 3.3 healOctaves） */
    var obsBest = -1, jumpSince = -1, jumpRef = 0, dispT = -1e9, dispMult = 1;  /* 這一次單獨看的最高點、突然跳的起點和跳到的值 */
    /* beatOn：可以顯示速度；everOn：這一輪聽過清楚的木魚（之後沒了才算「停了」）。
     * 0.5.1 起一開始也是 beatOn＝false，要跟「停了以後恢復」一樣聽到夠清楚的敲擊才顯示；
     * 原本一開始照單全收、顯示 20 秒後才判斷停了，地鐘還沒開始時講話、雜音、儀式聲都會先跑出數字 */
    var beatOn = false, everOn = false, lastBeatT = -1e9, stopBpm = null, resumeSince = -1, onSince = -1;
    var unclear = 0, everReset = false;            /* 還沒顯示時連續幾次不清楚；這一輪有沒有因為不清楚從頭抓過（畫面倒數用） */
    var tN = 0, tG = 0;                            /* 這次追蹤滿 trustSec 秒以後算了幾次、清楚幾次 */
    var GH = Math.round(6 / P.tempoEvery), gHist = new Uint8Array(GH), gN = 0;
    var TEMPO_EVERY_F = Math.max(1, Math.round(P.tempoEvery * FPS));
    var seg = new Float32Array(Math.ceil(P.tempoWin * FPS) + 2);
    /* 慢板格子（0.6）：最近的起音事件、候選間隔（0.43～1.4 秒，每格 1%） */
    var OKEEP = 512, onT = new Float64Array(OKEEP), onC = new Float32Array(OKEEP), onN = 0;
    var GP = [], gq;
    for (gq = 0; gq <= 120; gq++) GP.push(0.43 * Math.pow(1.4 / 0.43, gq / 120));
    var gridHist = [], gridBpm = 0, gridSince = -1, gridTick = 0, forceUntil = -1, gridStartT = -1e9;
    /* 地鐘儀表板（0.7）：畫面上的數字 dash、上次換數字的時間、換算的倍數；一直不一樣的起點和值；這一份出過數字沒 */
    var dash = 0, dashF = 1, lastCand = 0, sessionShown = false, stopT = -1e9, dashHist = [];   /* dashHist：最近畫面的數字 [時間, 速度] */

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
    function tNow() { return nFrames * HOP / TSR; }   /* 速度那邊的時間（跟 updateTempo 的 t 同一把尺） */

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
        if (isMax && c > 2.2 * mean + 1e-6 && tOn - lastOnsetT > 0.12) {
          lastOnsetT = tOn; onsetCount++;
          onT[onN % OKEEP] = tOn; onC[onN % OKEEP] = c; onN++;
        }
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
      if (P.grid && (gridTick++ & 1) === 0) gridUpdate(t);
      /* 太小聲（安靜的房間，只有冷氣、電器聲）或節奏不明確：不更新速度 */
      if (!sc || sc.conf < P.minConf || tempoLevel < P.minLevel) { tempoConf = sc ? sc.conf : 0; judgeBeat(t, false, nUpd * P.tempoEvery); dashUpdate(t); return; }
      tempoConf = sc.conf;
      if (lastGoodTempoT > 0 && t - lastGoodTempoT > 6 && !gridAgrees()) {   /* 停了一陣子再開始：重新抓（慢板格子還聽得到同樣的速度就不用） */
        V = null; nUpd = 0; mult = 1; lastOut = 0; bpmSmooth = 0; tN = tG = 0;
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
        if (den < 0) b = BMIN * Math.pow(2, (bi + Math.max(-0.5, Math.min(0.5, 0.5 * (a0 - c0) / den))) * LSTEP);
      }
      /* 地鐘只會越敲越快，突然變一半或兩倍不是真的。剛開始 10 秒還在找速度，不接 */
      if (lastOut && upSec > 10) {
        var dd = Math.log(b * mult / lastOut) / Math.LN2;
        if (Math.abs(dd) > 0.6) {
          var nm = mult * Math.pow(2, -Math.round(dd));
          if (nm >= 0.25 && nm <= 4 && b * nm >= BMIN * 0.9 && b * nm <= P.maxBpm * 1.05) mult = nm;   /* 0.7：接回後也要在速度範圍內 */
        }
      }
      b *= mult;
      lastOut = b;
      /* 以上是追速度本身（同 0.3.1）。以下只管畫面：
       * 這一次單獨看的最高點跟追蹤的對得上（含兩倍、一半、1.5 倍），才算「清楚的一次」，拿來判斷停了沒。
       * 畫面上的數字另外要求：不是貼著上限 maxBpm（收尾滾奏），也沒有突然跳（跳過去持續 jumpHold 秒才接受） */
      var dOct = obsBest >= 0 ? Math.abs(obsBest - bi) * LSTEP : 9;
      var agree = Math.min(dOct, Math.abs(dOct - 1), Math.abs(dOct - 0.585)) < P.agreeTol;
      /* 地鐘只會越敲越快：數字停住幾秒後，往上可以多跳一點（每秒 rampOct）；往下一次掉超過門檻就是收尾或雜音 */
      var jump = bpmSmooth > 0 && upSec > 10 &&
        Math.abs(Math.log(b / bpmSmooth) / Math.LN2) > P.jumpOct + (b > bpmSmooth ? P.rampOct * Math.max(0, t - dispT) : 0);
      /* 跳過去的值要穩定才累計（480 → 300 → 400 這樣一直換不算） */
      if (jump) {
        if (jumpSince < 0 || Math.abs(Math.log(b / jumpRef) / Math.LN2) > P.jumpOct / 2 + P.rampOct * (t - jumpSince)) { jumpSince = t; jumpRef = b; }
      } else jumpSince = -1;
      if (upSec >= P.trustSec) { tN++; if (agree) tG++; }   /* 追蹤滿 trustSec 秒以後，清楚的占幾成（畫面倒數用） */
      var seeded = judgeBeat(t, agree && upSec >= P.trustSec, upSec);
      if (!seeded && agree && beatOn && bi < M - 3 && (!jump || t - jumpSince >= P.jumpHold)) {
        bpmSmooth = bpmSmooth ? bpmSmooth + (b - bpmSmooth) * P.smooth : b;
        dispT = t; dispMult = mult;
      }
      dashUpdate(t);
    }

    /* ---------- 慢板格子（0.6） ---------- */
    function gridEval(t, hit) {
      var W = P.gridWin, t0 = t - W, ts = [], st = [], q;
      for (q = Math.max(0, onN - OKEEP); q < onN; q++) {
        var a = onT[q % OKEEP];
        if (a >= t0 && a <= t) { ts.push(a); st.push(onC[q % OKEEP]); }
      }
      var n = ts.length;
      if (n < 4) return null;
      var srt = st.slice().sort(function (x, y) { return x - y; });
      var med = n & 1 ? srt[n >> 1] : (srt[n / 2 - 1] + srt[n / 2]) / 2;
      if (!(med > 0)) return null;
      var strong = [], bigSum = 0;
      for (q = 0; q < n; q++) {
        st[q] /= med;
        if (st[q] >= hit) strong.push(q);
        if (st[q] >= P.gridOff) bigSum += st[q];
      }
      if (strong.length < 4) return null;
      var on = new Uint8Array(n), best = null;
      for (var pi = 0; pi < GP.length; pi++) {
        var per = GP[pi];
        if (Math.floor(W / per) < 5) continue;
        var w = P.gridTol * per;
        for (var si = 0; si < strong.length; si++) {
          var ph = (ts[strong[si]] - t0) % per, hits = 0, ng = 0, lo = 0, h;
          on.fill(0);
          for (var g = t0 + ph; g <= t; g += per) {
            ng++;
            while (lo < n && ts[lo] < g - w) lo++;
            var mx = 0;
            for (h = lo; h < n && ts[h] <= g + w; h++) { on[h] = 1; if (st[h] > mx) mx = st[h]; }
            if (mx >= hit) hits++;
          }
          var offS = 0;
          for (q = 0; q < n; q++) if (!on[q] && st[q] >= P.gridOff) offS += st[q];
          var scr = hits / ng - (bigSum > 0 ? offS / bigSum : 0);
          if (!best || scr > best.sc + 0.03 || (Math.abs(scr - best.sc) <= 0.03 && per > best.per)) best = { sc: scr, per: per };
        }
      }
      return best;
    }
    /* 每 0.5 秒：還沒顯示、顯示的速度在 gridMax 以下、或按了「地鐘開始了」以後 forceHold 秒內才算（快了就不用，省電） */
    function gridUpdate(t) {
      var shown = dash > 0 ? dash : bpmSmooth;
      if (beatOn && shown > 0 && shown >= P.gridMax * 1.15 && t >= forceUntil) { gridHist.length = 0; gridBpm = 0; return; }
      var b = gridEval(t, beatOn ? P.gridHitOn : P.gridHit);
      gridHist.push(b && b.sc >= P.gridScore && tempoLevel >= P.minLevel ? 60 / b.per : 0);
      if (gridHist.length > P.gridHold) gridHist.shift();
      gridBpm = 0;
      if (gridHist.length < P.gridHold) return;
      var v = gridHist.filter(function (x) { return x > 0; }).sort(function (x, y) { return x - y; });
      if (v.length < P.gridFrac * P.gridHold) return;
      var m = v.length & 1 ? v[v.length >> 1] : (v[v.length / 2 - 1] + v[v.length / 2]) / 2, ok = 0;
      for (var q = 0; q < v.length; q++) if (Math.abs(v[q] / m - 1) < P.gridTol2) ok++;
      if (ok >= P.gridFrac * P.gridHold && m >= Math.max(45, BMIN) && m <= P.gridMax) gridBpm = m;
    }
    /* 開始顯示，追蹤從這個速度接著抓（慢板格子、或按了「地鐘開始了」時已經有格子速度）。
     * 倍數接回以這個速度為準，追蹤跑到兩倍也會接回來 */
    /* 地鐘儀表板（0.7）：bpmSmooth 有新的值就決定畫面的數字。
     * 追到的速度、兩倍、一半，挑最接近最近 dashTrend 秒畫面數字中位數的那個（範圍外的不挑）。
     * 試過的：跟畫面上那一個數字比、差 7% 內才換算 → 畫面本身偏高時接不回來（0820 第 11 分 226 → 89）；也換算 1.5 倍、2/3 → 沒比較好；
     * 慢板格子決定倍數 → 90～130 格子會偏一半（0902、0922、舊金山變差），不用 */
    function dashUpdate(t) {
      if (!beatOn || !(bpmSmooth > 0) || bpmSmooth === lastCand) return;
      lastCand = bpmSmooth;
      var c = bpmSmooth, f = 1;
      /* 最近 dashTrend 秒的畫面數字；中間斷過（停了、沒更新）就用斷之前最後的那幾個（dashReset 秒內） */
      var last = dashHist.length ? dashHist[dashHist.length - 1][0] : -1e9;
      while (dashHist.length && dashHist[0][0] < Math.min(t, last + 1) - P.dashTrend) dashHist.shift();
      if (dashHist.length && t - last > P.dashReset) dashHist.length = 0;
      if (dashHist.length) {
        var v = dashHist.map(function (x) { return x[1]; }).sort(function (x, y) { return x - y; });
        var n = v.length, trend = n & 1 ? v[n >> 1] : (v[n / 2 - 1] + v[n / 2]) / 2, bd = 9, FS = [1, 0.5, 2];
        for (var q = 0; q < FS.length; q++) {
          var w = c * FS[q];
          if (w < BMIN * 0.97 || w > P.maxBpm) continue;
          var d = Math.abs(Math.log(w / trend));
          if (d < bd - 1e-9) { bd = d; f = FS[q]; }
        }
      }
      dash = Math.max(BMIN, Math.min(P.maxBpm, c * f)); dashF = f; sessionShown = true;
      dashHist.push([t, dash]);
    }

    /* 顯示中、慢板格子聽到的速度跟畫面一樣（差 7% 內）：唱誦蓋過木魚、上面的節奏明確度不夠時，數字照樣留著 */
    function gridAgrees() {
      var ref = dash > 0 ? dash : bpmSmooth;
      return beatOn && gridBpm > 0 && ref > 0 && Math.abs(Math.log(gridBpm / ref) / Math.LN2) < 0.1;
    }
    /* 恢復顯示：停太久（dashReset 秒）當作新的一次地鐘，不接著之前的數字 */
    function dashResume(t) {
      if (t - stopT > P.dashReset) { dash = 0; dashF = 1; dashHist.length = 0; }
      lastCand = 0;
    }
    function seedAt(t, bpm) {
      if (!beatOn) dashResume(t);
      dashHist.length = 0;   /* 格子給的速度是刻意的修正，不跟之前畫面上的數字比 */
      beatOn = true; everOn = true; resumeSince = -1; onSince = t; unclear = 0; gridSince = -1; gridHist.length = 0;
      var j0 = Math.max(0, Math.min(M - 1, Math.round(Math.log(bpm / BMIN) / Math.LN2 / LSTEP)));
      V = new Float32Array(M);
      for (var j = 0; j < M; j++) V[j] = -2 * Math.abs(j - j0) * LSTEP;
      nUpd = Math.ceil(10 / P.tempoEvery) + 1; tempoIdx = j0; lastGoodTempoT = t;
      mult = 1; lastOut = bpm; bpmSmooth = bpm; dispT = t; dispMult = 1; jumpSince = -1; tN = tG = 0;
    }

    function clarity() {
      var s = 0, n = Math.min(gN, GH);
      for (var q = 0; q < n; q++) s += gHist[q];
      return n ? s / n : 0;
    }

    /* 有沒有在敲：顯示中超過 stopBeats 下（至少 stopMin 秒）沒有清楚的一次 → 停了（畫面停在最後的速度）；
     * 剛開始聽、停了以後，都要最近 6 秒九成左右都清楚、持續 resumeSec 秒才顯示，講話、雜音不會讓數字跑出來 */
    function judgeBeat(t, good, upSec) {
      gHist[gN % GH] = good ? 1 : 0; gN++;
      if (beatOn) {
        /* 按了「地鐘開始了」以後 forceHold 秒內：數字還沒出來、或畫面的速度跟格子不一樣又不是一直都清楚（按得早，追到開頭的雜音或倍數），
         * 格子聽到慢板速度就改從那個速度接著算。數字已經出來、木魚又清楚時按鈕不會出現，所以這段時間幾乎都是地鐘剛開始的慢板 */
        if (t < forceUntil && gridBpm && (bpmSmooth <= 0 || upSec < 10 || (!gridAgrees() && clarity() < P.resumeFrac))) { seedAt(t, gridBpm); return true; }
        var ref = dash > 0 ? dash : bpmSmooth > 0 ? bpmSmooth : lastOut, per = ref > 0 ? 60 / ref : 0.2;   /* 用畫面上的速度（雜音裡接的倍數不算） */
        /* 慢板：格子聽得到、速度跟畫面一樣，也算有在敲（開頭慢板「對得上」常常不成立，免得被判成停了） */
        if (good || (gridBpm && ref > 0 && Math.abs(Math.log(gridBpm / ref) / Math.LN2) < 0.1)) lastBeatT = t;
        if (onSince < 0 && upSec > 10) onSince = t;     /* 開始顯示 */
        if (t >= forceUntil && onSince >= 0 && t - onSince >= P.stopAfter && lastBeatT > -1e8 && t - lastBeatT > Math.max(P.stopMin, P.stopBeats * per)) {
          beatOn = false; resumeSince = -1; onSince = -1;
          stopBpm = dash > 0 ? dash : bpmSmooth > 0 ? bpmSmooth : null; gridHist.length = 0; gridBpm = 0; stopT = t; lastCand = 0;
          if (t - gridStartT < P.probation) { everOn = false; stopBpm = null; lastBeatT = -1e9; dash = 0; sessionShown = false; dashHist.length = 0; }   /* 靠格子剛開始顯示就停了：當作沒聽到過 */
          gridStartT = -1e9;
          V = null; nUpd = 0; mult = 1; lastOut = 0; bpmSmooth = 0; jumpSince = -1; dispMult = 1; tN = tG = 0;   /* 重新開始時從頭抓 */
        }
      } else {
        if (good) lastBeatT = t;
        /* 慢板格子連續聽清楚 resumeSec 秒：從格子的速度開始顯示 */
        if (gridBpm) {
          if (gridSince < 0) gridSince = t;
          if (t - gridSince >= P.gridStart) { seedAt(t, gridBpm); gridStartT = t; return true; }
        } else gridSince = -1;
        var s = 0;
        for (var q = 0; q < GH; q++) s += gHist[q];
        if (gN >= GH && s / GH >= P.resumeFrac) {
          if (resumeSince < 0) resumeSince = t;
          /* 這一份還沒出過數字、速度又快（地鐘開頭不會這麼快）：要清楚得久一點 */
          var need = !sessionShown && tempoIdx >= 0 && BPMS[tempoIdx] * mult > P.fastStart ? P.fastStartSec : P.resumeSec;
          if (t - resumeSince >= need) {           /* 開始／恢復：停了那段雜音裡接的倍數不算 */
            dashResume(t);
            beatOn = true; everOn = true; resumeSince = -1; onSince = t; mult = 1; lastOut = tempoIdx >= 0 ? BPMS[tempoIdx] : 0;
            unclear = 0;
            return;
          }
        } else resumeSince = -1;
        /* 還沒顯示：連續 resetSec 秒都不清楚 → 追蹤從頭抓 */
        if (good) unclear = 0;
        else if (upSec >= P.trustSec) unclear++;
        if (unclear * P.tempoEvery >= P.resetSec) {
          V = null; nUpd = 0; mult = 1; lastOut = 0; unclear = 0; everReset = true; tN = tG = 0;
        }
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
      var fold = recent.map(function (p) {           /* 0.5 起折回剛好一個八度（中心上下各 6 個半音），原本上下 9 個 */
        var v = p.m;
        while (v < c - 6) v += 12;
        while (v >= c + 6) v -= 12;
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
      var key = null, ah = keyPts.length >= 30 ? ahClass(keyPts) : null;
      if (ah) {
        var pc = ah.pc;
        /* 「阿」偶爾唱得少，最低的常唱音會一下跳成上面的「彌」：往上跳時，上一次（15 秒內）的「阿」這次還聽得到就接著用。
         * 往下跳（出現更低的常唱音）照樣採用，免得開頭量錯就一路錯下去 */
        if (lastKey != null && t - lastKeyT <= 15 && circ(pc - lastKey) > 0.8) {
          var alt = null;
          ah.bands.forEach(function (b) {
            var d = Math.abs(circ(b - lastKey));
            if (d <= 0.6 && (alt == null || d < Math.abs(circ(alt - lastKey)))) alt = b;
          });
          if (alt != null) pc = alt;
        }
        /* 音名 → 音高：離上一次（1 分鐘內）最近的八度；第一次、隔太久放在標準「阿」A3（57）附近。
         * 0.5.1 起限制在 C3～A4（48～69）：不是唱誦的聲音（拜佛、開示）讓音名一直繞圈時，原本會一路往下飄（實測 9-11 共修錄音飄到 −300） */
        var ref = lastKey != null && t - lastKeyT <= 60 ? lastKey : 57;
        key = pc + 12 * Math.round((ref - pc) / 12);
        while (key < 48) key += 12;
        while (key > 69) key -= 12;
        lastKey = key; lastKeyT = t;
      }
      return { note: note, key: key, keyN: keyPts.length, center: c };
    }
    var lastKey = null, lastKeyT = -1e9;

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
      var live = beatOn && bpmSmooth > 0 && dash > 0 && tempoIdx >= 0 && nUpd * P.tempoEvery >= 10 && (t - lastGoodTempoT < 4 || gridAgrees());   /* 剛開始 10 秒的估計還在跳，不顯示 */
      /* 開頭取樣：先收 4 秒聲音才算第一次；追蹤 trustSec 秒以後，最近 6 秒 85% 清楚、持續 3 秒才顯示，順利的話追蹤約 14.5 秒。給畫面倒數用 */
      var warm = null, upSec = nUpd * P.tempoEvery, WARM = beatOn ? 10 : 14.5;   /* 按了「地鐘開始了」：追蹤滿 10 秒就顯示 */
      if (!everOn || (beatOn && (upSec < 10 || bpmSmooth <= 0))) {
        var left = Math.max(0, 4 - nFrames / FPS) + Math.max(0, WARM - upSec);
        /* 沒聽到清楚的木魚聲：倒數停住、顯示等木魚聲。因為不清楚從頭抓過以後，要追蹤滿 trustSec 秒、確定清楚才再倒數 */
        var trusted = upSec >= P.trustSec;
        var stalled = nFrames >= FPS * 4 && !beatOn && (t - lastGoodTempoT > 1.5 || (everReset && !trusted) ||
                      (trusted && (t - lastBeatT > 1 || (tN && tG / tN < P.resumeFrac))) || upSec >= WARM);
        warm = { left: left, frac: stalled && (everReset || trusted) ? 0 : Math.max(0, Math.min(1, 1 - left / (WARM + 4))), stalled: stalled };
      }
      return {
        t: t,
        bpm: live ? dash : null,
        stopped: everOn && !beatOn,       /* 判斷成停了（地鐘結束、只剩講話或雜音）；還沒聽到過清楚的木魚不算 */
        lastBpm: everOn && !beatOn ? stopBpm : null, /* 停之前最後的速度 */
        tempoConf: tempoConf,
        tempoPeak: tempoPeak,
        tempoLevel: tempoLevel,           /* 最近幾秒高頻音量的高點（dBFS） */
        autoMult: Math.round(dispMult * dashF * 100) / 100,   /* 1 以外＝自動接回過倍數（畫面上那個數字用的；0.7 起含儀表板換算的 2/3、1.5） */
        lastOnsetAgo: lastOnsetT >= 0 ? t - lastOnsetT : null,
        onsets: onsetCount,
        note: cachedPitch.note,          /* 現在唱的音（半音刻度，可帶小數） */
        key: cachedPitch.key,            /* 現在的調：四字佛號「阿」的音 */
        keyN: cachedPitch.keyN,
        keyFrac: cachedPitch.key != null ? 1 : Math.min(1, cachedPitch.keyN / 30),   /* 調的取樣進度（唱得穩的點要 30 個） */
        warm: warm,                       /* 速度還在取樣：{ left 剩幾秒, frac 進度, stalled 等木魚聲 }，其他時候 null */
        clarity: clarity(),               /* 最近 6 秒「清楚的一次」占幾成（測試用） */
        gridBpm: gridBpm,                 /* 慢板格子聽到的速度，0＝沒有（測試用） */
        canForce: !beatOn,                /* 可以按「地鐘開始了」（還沒顯示數字、或判斷成停了） */
        forced: tNow() < forceUntil       /* 按了「地鐘開始了」以後 forceHold 秒內（不判斷停了） */
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
    /* 使用者停止後重新按開始：已經判斷成停了的話，回到剛開始聽的樣子（顯示取樣中，聽到清楚的木魚才出數字） */
    api.rearm = function () { if (!beatOn) { everOn = false; stopBpm = null; lastBeatT = -1e9; resumeSince = -1; onSince = -1; unclear = 0; everReset = false; } };
    /* 「地鐘開始了」：不等木魚聲聽清楚，追蹤滿 10 秒就顯示（已經有格子速度就從那個速度直接顯示）；forceHold 秒內不判斷停了 */
    api.force = function () {
      if (beatOn) return;
      var t = tNow();
      if (gridBpm) seedAt(t, gridBpm);
      else { dashResume(t); beatOn = true; everOn = true; resumeSince = -1; onSince = -1; unclear = 0; gridSince = -1; gridHist.length = 0; }
      forceUntil = t + P.forceHold; gridStartT = -1e9;
    };
    api.sampleRate = SR;
    return api;
  }

  var DZ = { createEngine: createEngine, noteOf: noteOf, toMidi: toMidi, midiToHz: midiToHz, NOTE_NAMES: NOTE_NAMES };
  if (typeof module !== "undefined" && module.exports) module.exports = DZ;
  else root.DZ = DZ;
})(typeof self !== "undefined" ? self : this);
