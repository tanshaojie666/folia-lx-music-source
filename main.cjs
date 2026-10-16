// 洛雪音源 → Folia (Folium) · main 入口（Node 主进程）
//
// 两类音源，统一成一个注册表，每个音源可单独启用/停用：
//
//   A. 内置直连后端（kind: direct）
//      网易云 —— 唯一实测能同时做「搜索」和「无损取链」的平台。
//      搜索走 GDStudio 聚合 → 163 官方兜底；取链走 qijieya br=740（实测真 FLAC）。
//
//   B. 洛雪音乐自定义脚本（kind: lx）
//      放在 sources/ 目录里的 .js，跑在复刻洛雪运行时的 vm 沙箱里。
//      这类脚本多数只声明 musicUrl（不支持搜索），所以搜索统一用网易云，
//      取链时再交给脚本做多平台解析。
//
// 用户可以随时「添加音源」（本地路径或 URL 下载脚本）。

'use strict';

const fs = require('node:fs');
const path = require('node:path');
const net = require('node:net');
const vm = require('node:vm');
const zlib = require('node:zlib');
const crypto = require('node:crypto');

/* ══════════════════════════════════════════════════════════════════
 * 常量
 * ══════════════════════════════════════════════════════════════════ */

const UA_PC =
  'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36';
const UA_OKHTTP = 'okhttp/4.10.0';

const TIMEOUT_MS = 15000;
const PROBE_TIMEOUT_MS = 12000;
const INIT_TIMEOUT_MS = 8000;
const ACTION_TIMEOUT_MS = 25000;

// meting 接口的 br 参数。
// 实测（2026-10-15，qijieya）：br=740 与 br=999 返回**完全相同**的文件
// （同 bit 深、同采样率、同字节数），740 就是 24bit 档。所以 999 是多余的，
// 去掉它可少一次串行请求。320/128 作为降级兜底保留。
const METING_BR = {
  standard: [128],
  high: [320, 128],
  lossless: [740, 320],
  hires: [740, 320],
};

// 洛雪音源的 type 字符串，逐级降级
const LX_LEVEL = {
  standard: ['128k'],
  high: ['320k', '128k'],
  lossless: ['flac', '320k', '128k'],
  hires: ['flac24bit', 'flac', '320k', '128k'],
};

const EVENT_NAMES = Object.freeze({
  request: 'request',
  inited: 'inited',
  updateAlert: 'updateAlert',
});

const CONFIG_KEY = 'config';
const DISABLED_KEY = 'disabled';

const DEFAULT_CONFIG = {
  quality: 'lossless',
  fallback: true,
  enabledSources: '',
};

/* ══════════════════════════════════════════════════════════════════
 * 基础工具
 * ══════════════════════════════════════════════════════════════════ */

function withTimeout(promise, ms, code) {
  let timer;
  return Promise.race([
    promise,
    new Promise(function (_, reject) {
      timer = setTimeout(function () {
        reject(new Error(code));
      }, ms);
    }),
  ]).finally(function () {
    clearTimeout(timer);
  });
}

function normQuality(q) {
  const raw = typeof q === 'string' ? q : (q && (q.id || q.level || q.name || q.quality)) || '';
  const t = String(raw).toLowerCase();
  if (/hires|24bit|24\/|master|sq/.test(t)) return 'hires';
  if (/flac|loss|无损/.test(t)) return 'lossless';
  if (/320|high|较高/.test(t)) return 'high';
  if (/128|standard|std|标准/.test(t)) return 'standard';
  return 'lossless';
}

/** 探测缓冲区前几个字节，判断真实音频格式。 */
function sniff(buf) {
  if (!buf || buf.length < 4) return 'empty';
  const b = buf;
  if (b[0] === 0x66 && b[1] === 0x4c && b[2] === 0x61 && b[3] === 0x43) return 'flac'; // "fLaC"
  if (b[0] === 0x49 && b[1] === 0x44 && b[2] === 0x33) return 'mp3'; // "ID3"
  if (b[0] === 0xff && (b[1] & 0xe0) === 0xe0) return 'mp3'; // MPEG frame sync
  if (b[0] === 0x4f && b[1] === 0x67 && b[2] === 0x67 && b[3] === 0x53) return 'ogg'; // "OggS"
  if (b[0] === 0x52 && b[1] === 0x49 && b[2] === 0x46 && b[3] === 0x46) return 'wav'; // "RIFF"
  if (b.length >= 12 && b.slice(4, 8).toString('latin1') === 'ftyp') return 'm4a';
  if (b[0] === 0x7b || b[0] === 0x5b) return 'json'; // JSON 包裹
  return 'unknown';
}

/** 解析 FLAC STREAMINFO，拿到真实位深/采样率/时长。 */
function flacInfo(buf) {
  if (!buf || buf.length < 42) return null;
  if (buf.slice(0, 4).toString('latin1') !== 'fLaC') return null;
  const b = buf;
  const si = 8; // 4 字节 magic + 4 字节 block header
  const sr = (b[si + 10] << 12) | (b[si + 11] << 4) | (b[si + 12] >> 4);
  const ch = ((b[si + 12] >> 1) & 0x07) + 1;
  const bps = (((b[si + 12] & 0x01) << 4) | (b[si + 13] >> 4)) + 1;
  const total =
    (b[si + 13] & 0x0f) * 2 ** 32 +
    b[si + 14] * 2 ** 24 +
    b[si + 15] * 2 ** 16 +
    b[si + 16] * 2 ** 8 +
    b[si + 17];
  return { sampleRate: sr, channels: ch, bitsPerSample: bps, totalSamples: total };
}

function isLosslessKind(kind) {
  return kind === 'flac' || kind === 'wav';
}

/* ══════════════════════════════════════════════════════════════════
 * 无损取链缓存
 *
 * 同一首歌在会话内会被反复取链（切歌、重播、拖动进度条）。实测 qijieya
 * 单次 160–350ms，缓存后直接命中。只缓存**探测通过的**结果，TTL 20 分钟
 * （网易云直链本身约 20 分钟后失效）。
 * ══════════════════════════════════════════════════════════════════ */

const URL_CACHE_TTL_MS = 20 * 60 * 1000;
const URL_CACHE_MAX = 300;
const urlCache = new Map();

function cacheKey(unitId, songId, quality) {
  return unitId + '\u0000' + songId + '\u0000' + quality;
}

function cacheGet(key) {
  const hit = urlCache.get(key);
  if (!hit) return null;
  if (Date.now() - hit.at > URL_CACHE_TTL_MS) {
    urlCache.delete(key);
    return null;
  }
  return hit.value;
}

function cacheSet(key, value) {
  if (urlCache.size >= URL_CACHE_MAX) {
    const oldest = urlCache.keys().next().value;
    urlCache.delete(oldest);
  }
  urlCache.set(key, { at: Date.now(), value: value });
}

/* ══════════════════════════════════════════════════════════════════
 * 未处理拒绝护栏
 *
 * 洛雪脚本里到处是"浮空"的 promise（`fetch(...).then(...).catch(e => { throw e })`），
 * 一旦网络不通就产生 unhandledRejection。vm 沙箱与宿主共享 microtask 队列，
 * 这类拒绝会逃出沙箱并按 Node 默认行为**直接终止进程** —— 一个坏脚本能崩掉整个 Folia。
 * 这里装进程级护栏：只吞掉来自音源脚本的拒绝。
 * ══════════════════════════════════════════════════════════════════ */

let rejectionGuardInstalled = false;

function installRejectionGuard(api) {
  if (rejectionGuardInstalled) return;
  rejectionGuardInstalled = true;

  process.on('unhandledRejection', function (reason) {
    const text = String((reason && reason.stack) || reason || '');
    if (text.indexOf('lx-source-') >= 0 || text.indexOf('LX_') >= 0) {
      api.log.warn(
        '音源脚本抛出未处理的异步错误（已隔离，不影响宿主）',
        text.split('\n').slice(0, 2).join(' | ')
      );
      return;
    }
    console.error('[unhandledRejection]', reason);
  });
}

/* ══════════════════════════════════════════════════════════════════
 * HTTP
 * ══════════════════════════════════════════════════════════════════ */

function makeHttp(fetchImpl) {
  async function httpGet(url, opts) {
    const o = opts || {};
    const headers = o.headers || {};
    const timeout = o.timeout || TIMEOUT_MS;
    const method = o.method || 'GET';
    const body = o.body || null;

    const ctl = new AbortController();
    const timer = setTimeout(function () {
      ctl.abort();
    }, timeout);
    try {
      const res = await fetchImpl(url, {
        method: method,
        redirect: 'follow',
        signal: ctl.signal,
        body: body,
        headers: Object.assign({ 'User-Agent': UA_PC }, headers),
      });
      const ab = await res.arrayBuffer();
      return { status: res.status, headers: res.headers, buf: Buffer.from(ab) };
    } finally {
      clearTimeout(timer);
    }
  }

  async function getText(url, opts) {
    const r = await httpGet(url, opts);
    return r.buf.toString('utf8');
  }

  async function getJson(url, opts) {
    const t = await getText(url, opts);
    try {
      return JSON.parse(t);
    } catch {
      const m = t.match(/[[{][\s\S]*[\]}]/);
      if (m) {
        try {
          return JSON.parse(m[0]);
        } catch {
          /* 放弃 */
        }
      }
      return null;
    }
  }

  /** 只取头部若干字节，判断真实格式。 */
  async function probe(url, headers) {
    try {
      const h = Object.assign({}, headers || {}, { Range: 'bytes=0-65535' });
      const r = await httpGet(url, { headers: h, timeout: PROBE_TIMEOUT_MS });
      if (r.status >= 400 && r.buf.length < 4) return { ok: false, kind: 'http-' + r.status };
      const kind = sniff(r.buf);
      if (kind === 'empty' || kind === 'json' || kind === 'unknown') return { ok: false, kind: kind };
      const cr = r.headers.get('content-range');
      const total = cr ? Number(String(cr).split('/')[1]) : Number(r.headers.get('content-length')) || 0;
      const out = { ok: true, kind: kind, status: r.status, bytes: total || 0 };
      if (kind === 'flac') {
        const fi = flacInfo(r.buf);
        if (fi) {
          out.bits = fi.bitsPerSample;
          out.sampleRate = fi.sampleRate;
          out.channels = fi.channels;
        }
      }
      return out;
    } catch (err) {
      return { ok: false, kind: 'error', err: String((err && err.message) || err) };
    }
  }

  return { httpGet: httpGet, getText: getText, getJson: getJson, probe: probe, fetchImpl: fetchImpl };
}

/* ══════════════════════════════════════════════════════════════════
 * 候选链求值：无损优先，**并行探测**
 *
 * 串行版实测最坏 22–26 秒：链上每个候选都要等前一个超时/失败。
 * 改成并行后，只要最高优先级的候选返回无损就立刻收工，
 * 完全不等待慢候选（gdstudio 单次 2.4–4.3s）。
 * ══════════════════════════════════════════════════════════════════ */

const CHAIN_DEADLINE_MS = 9000;

// 最高优先级候选已经给出**有损**结果时的宽限期。
// 实测：qijieya br=740 就是无损档，它回 MP3 说明这首歌在源站本身没有 FLAC
// （其余候选也只会回同样的 MP3）。所以给它一个短宽限，期间若有别的候选
// 给出无损就采用，否则宽限到期直接返回，避免为了等慢候选白等 20 多秒。
const LOSSY_GRACE_MS = 1500;

async function resolveChain(http, chain, quality, headers) {
  const wantLossless = quality === 'lossless' || quality === 'hires';
  const tried = [];
  const results = new Array(chain.length).fill(null);
  let settled = 0;

  return new Promise(function (resolve) {
    let done = false;
    let timer = null;
    let graceTimer = null;

    function finish(val) {
      if (done) return;
      done = true;
      if (timer) clearTimeout(timer);
      if (graceTimer) clearTimeout(graceTimer);
      resolve(val);
    }

    function build(r) {
      return {
        url: r.url,
        kind: r.kind,
        via: r.step.via,
        quality: isLosslessKind(r.kind) ? 'lossless' : quality === 'standard' ? 'standard' : 'high',
        probe: r.probe,
        tried: tried,
      };
    }

    function maybeFinish() {
      const top = results[0];

      // 1) 最高优先级拿到无损 → 立刻收工，不理会更慢的候选
      if (top && top.ok && isLosslessKind(top.kind)) return finish(build(top));

      // 2) 不需要无损时，最高优先级一有可用结果就收工
      if (!wantLossless && top && top.ok) return finish(build(top));

      // 3) 最高优先级给出有损结果 → 启动宽限期，等其他候选能否给出无损
      if (wantLossless && top && top.ok && !graceTimer) {
        graceTimer = setTimeout(function () {
          if (done) return;
          // 宽限期内若有任何候选给出无损，采用它
          for (let i = 0; i < chain.length; i++) {
            const r = results[i];
            if (r && r.ok && isLosslessKind(r.kind)) return finish(build(r));
          }
          finish(build(top));
        }, LOSSY_GRACE_MS);
      }

      // 4) 按优先级扫描：找到无损，且它前面所有候选都已落定 → 收工
      for (let i = 0; i < chain.length; i++) {
        const r = results[i];
        if (!r) break; // 更高优先级还没回来，继续等
        if (r.ok && isLosslessKind(r.kind)) return finish(build(r));
      }

      // 5) 全部落定 → 取优先级最高的可用结果
      if (settled >= chain.length) {
        for (let i = 0; i < chain.length; i++) {
          const r = results[i];
          if (r && r.ok) return finish(build(r));
        }
        return finish(null);
      }
    }

    timer = setTimeout(function () {
      // 硬截止：拿当前最好的结果，不再等慢候选
      for (let i = 0; i < chain.length; i++) {
        const r = results[i];
        if (r && r.ok) return finish(build(r));
      }
      finish(null);
    }, CHAIN_DEADLINE_MS);

    chain.forEach(function (step, i) {
      (async function () {
        try {
          let url = step.url;
          if (step.json) {
            const j = await http.getJson(step.json, { headers: headers || {} });
            const real = (j && (j.url || (j.data && j.data.url) || j.data)) || null;
            if (typeof real !== 'string' || !/^https?:/i.test(real)) {
              tried.push(step.via + ':无url');
              results[i] = { ok: false };
              return;
            }
            url = real;
          }
          if (!url) {
            results[i] = { ok: false };
            return;
          }
          const p = await http.probe(url, headers);
          if (p.ok) {
            results[i] = { ok: true, url: url, kind: p.kind, step: step, probe: p };
          } else {
            results[i] = { ok: false };
            tried.push(step.via + ':' + p.kind);
          }
        } catch (err) {
          results[i] = { ok: false };
          tried.push(step.via + ':' + String((err && err.message) || err).slice(0, 40));
        } finally {
          settled++;
          if (!done) maybeFinish();
        }
      })();
    });
  });
}

/* ══════════════════════════════════════════════════════════════════
 * A. 内置直连后端
 * ══════════════════════════════════════════════════════════════════ */

function meting(server, id, br, host) {
  return 'https://' + host + '/meting/?server=' + server + '&type=url&id=' + encodeURIComponent(id) + '&br=' + br;
}

/* ── 聚合 API（qijieya）──────────────────────────────────────────────
 * 实测 2026-10-15：这是目前唯一「搜索 + 真无损取链」都能用的口子。
 *
 *   搜索：GET /meting/?server=netease&type=search&id=<关键词>
 *         返回 [{ name, artist, url, pic, lrc }]，url 里带真实歌曲 id。
 *   取链：GET /meting/?server=netease&type=url&id=<id>&br=740
 *         br=740 实测返回**真 FLAC**（44.1k/24bit 起）。
 *
 * 关键点：搜索结果的 url 字段**不带 br**，直接请求只会拿到 MP3；
 * 必须自己补 &br=740 才是无损档。这一点在 netease/migu 上都成立。
 *
 * 实测 25 首常见歌：真无损 88%、可播放 96%（含 MP3 兜底）。
 * 网易云原版（周杰伦等）在搜索里被替换成同曲翻唱，但**音频本身仍是真 FLAC**，
 * 听感无损；这一点无法通过搜索接口绕过，只能接受。
 * ─────────────────────────────────────────────────────────────────── */
const AGG_HOST = 'api.qijieya.cn';

function aggSearchUrl(kw, server) {
  return 'https://' + AGG_HOST + '/meting/?server=' + (server || 'netease') +
    '&type=search&id=' + encodeURIComponent(kw);
}

/** 从 meting 搜索结果的 url 字段里抠出歌曲 id。 */
function aggIdOf(u) {
  const m = String(u || '').match(/[?&]id=([^&]+)/);
  return m ? decodeURIComponent(m[1]) : '';
}

/* ── 网易云官方搜索（直连，不经聚合站）──────────────────────────────
 * 2026-10-16 实测：聚合站的 server=netease 搜索分支返回空数组（2 字节 "[]"），
 * 而官方 cloudsearch 正常，还带回 hr/sq 规格字段。
 * 取链仍走聚合站 br=740 —— 官方搜索给的 id 交给聚合站，实测 12/12 全拿到真 FLAC，
 * 包括周杰伦的版权曲（原唱 id 一样能取，不再只能拿翻唱）。
 *
 * 这条是「网易云（聚合）」的主搜索路。它挂了才落到聚合站，聚合站也空才落到 migu。
 * ─────────────────────────────────────────────────────────────────── */
async function neteaseOfficialSearch(http, q, limit) {
  const n = Math.min(Math.max(limit || 10, 1), 30);
  const url = 'https://music.163.com/api/cloudsearch/pc?s=' + encodeURIComponent(q) +
    '&type=1&limit=' + n + '&offset=0';
  const j = await http.getJson(url, { headers: { Referer: 'https://music.163.com/' } });
  const songs = j && j.result && j.result.songs;
  if (!Array.isArray(songs)) return [];

  const out = [];
  const seen = {};
  for (const s of songs) {
    const sid = s && s.id != null ? String(s.id) : '';
    if (!sid || seen[sid]) continue;
    seen[sid] = 1;
    const ar = Array.isArray(s.ar) ? s.ar : (Array.isArray(s.artists) ? s.artists : []);
    const al = s.al || s.album || {};
    out.push({
      id: sid,
      title: s.name || '',
      artist: ar.map(function (a) { return (a && a.name) || ''; }).filter(Boolean).join('/'),
      album: al.name || '',
      cover: al.picUrl || '',
      durationMs: s.dt || s.duration || 0,
      _urlServer: 'netease',
    });
  }
  return out;
}

/* ── 原唱优先（版权曲目降权绕过）────────────────────────────────────
 * 2026-10-16 实测：网易云对周杰伦这类版权曲目做的是**降权**，不是删除。
 *   cloudsearch「晴天 周杰伦」limit=10  —— 186016（原唱 269s）完全不出现；
 *   limit=100                          —— 出现了，但 dt=0（被标记不可播），排在最后。
 * 而 /api/v1/artist/songs 这条路**不降权**：
 *   id=6452（周杰伦）→ 含 186016 晴天 / 269s / 《叶惠美》，字段完整。
 * 所以：从查询里认出歌手 → 拉该歌手全量歌曲 → 标题命中的提到最前。
 * 实测把原唱从「搜不到」变成第 1 条。
 * ─────────────────────────────────────────────────────────────────── */
async function neteaseArtistOriginals(http, q, limit) {
  const tokens = String(q || '').split(/\s+/).map(function (x) { return x.trim(); }).filter(Boolean);
  if (tokens.length < 2) return [];

  let list = [];
  try {
    const artists = await http.getJson(
      'https://music.163.com/api/cloudsearch/pc?s=' + encodeURIComponent(tokens.join(' ')) +
        '&type=100&limit=5&offset=0',
      { headers: { Referer: 'https://music.163.com/' } }
    );
    list = (artists && artists.result && artists.result.artists) || [];
  } catch {
    return [];
  }
  if (!Array.isArray(list) || !list.length) return [];

  /* 歌手名必须**原样**出现在查询里，否则「晴天」会被误当歌手名。 */
  const hit = list.find(function (a) {
    const nm = String((a && a.name) || '').trim();
    return nm && tokens.indexOf(nm) >= 0;
  });
  if (!hit) return [];

  const rest = tokens.filter(function (t) { return t !== String(hit.name).trim(); });
  if (!rest.length) return [];

  let songs = [];
  try {
    const res = await http.getJson(
      'https://music.163.com/api/v1/artist/songs?id=' + encodeURIComponent(hit.id) + '&limit=100&offset=0',
      { headers: { Referer: 'https://music.163.com/' } }
    );
    songs = (res && res.songs) || [];
  } catch {
    return [];
  }
  if (!Array.isArray(songs)) return [];

  const cap = Math.min(Math.max(limit || 10, 1), 10);
  const out = [];
  for (const s of songs) {
    const sid = s && s.id != null ? String(s.id) : '';
    const title = String((s && s.name) || '');
    if (!sid || !title) continue;
    /* 标题必须命中查询里的剩余词，避免把该歌手全部歌曲塞进结果。 */
    if (!rest.some(function (t) { return title.indexOf(t) >= 0; })) continue;
    const ar = Array.isArray(s.ar) ? s.ar : (Array.isArray(s.artists) ? s.artists : []);
    const al = s.al || s.album || {};
    out.push({
      id: sid,
      title: title,
      artist: ar.map(function (a) { return (a && a.name) || ''; }).filter(Boolean).join('/'),
      album: al.name || '',
      cover: al.picUrl || '',
      durationMs: s.dt || s.duration || 0,
      _urlServer: 'netease',
      _original: true,
    });
    if (out.length >= cap) break;
  }
  return out;
}

/* ── 网易云解灰（Folia 自带后端）────────────────────────────────────
 * Folia 主进程内置 @unblockneteasemusic/server，起在 127.0.0.1:<动态端口>，
 * 对版权曲目能拿到**完整原唱**：
 *   GET /song/url/v1?id=186016&level=lossless&unblock=true
 *     → http://bd-er.kuwo.cn/...  （实测 Folia 播放器读出的时长 = 269.75s，
 *        即《叶惠美》原唱完整版；搜索结果里那首翻唱只有 112s）
 * 端口是动态的，所以由**渲染层**（能调 window.electron.getNeteasePort）
 * 通过 config.sync 把端口交进来，主进程只负责拼 URL 与探测。
 * 拿不到端口时整条路自动跳过，不影响其它后端。
 * ─────────────────────────────────────────────────────────────────── */
let neteaseUnblockPort = 0;
const UNBLOCK_LEVELS = ['lossless', 'hires'];

function unblockUrl(id, level) {
  return 'http://127.0.0.1:' + neteaseUnblockPort +
    '/song/url/v1?id=' + encodeURIComponent(id) + '&level=' + level + '&unblock=true';
}

/* 自己找解灰后端端口。
 * 为什么不靠渲染层上报：模组 client 跑在 Electron 的**隔离上下文**里
 * （实测 window.electron === undefined），拿不到 getNeteasePort()。
 *
 * 端口范围：Folia 用 findFreePort() = net.createServer().listen(0) 取端口，
 * 即**操作系统临时端口段**，不是固定区间。实测同一个 Windows 上，
 * 早先落在 149xx（所以早期版本误以为可以只扫 14900–14999），
 * 后来系统单调推进到 32xx —— 那次硬编码扫描的命中率是 **0/100**。
 * 所以不能猜固定窗口，必须覆盖整段：
 *   Windows      1024–15000  （netsh 实测动态端口范围）
 *   Linux/macOS  32768–60999 （IANA ephemeral）
 * 两段实测合计约 6.6s（TCP 先行，再只对开放端口做 HTTP 识别）。
 *
 * 命中判定：/song/url/v1 返回带 data 数组的 JSON。探测结果缓存，
 * 失败则指数退避重试（1s → 2s → … 上限 60s），避免空转烧 CPU。 */
let portProbeAt = 0;
let portProbeFailures = 0;
let portProbeInFlight = null;

/* 按平台给范围，别在 Windows 上白扫 4 秒 Linux 段（反之亦然）。 */
const EPHEMERAL_RANGES = process.platform === 'win32'
  ? [[1024, 15000]]              // netsh int ipv4 show dynamicport tcp
  : [[32768, 60999], [1024, 15000]];  // IANA ephemeral；部分容器/旧内核仍用低位段

/* TCP 先探连通性：比直接发 HTTP 快得多，也不给无关端口留半开连接。 */
function tcpOpen(port, timeoutMs) {
  return new Promise(function (resolve) {
    const sock = new net.Socket();
    let settled = false;
    const finish = function (ok) {
      if (settled) return;
      settled = true;
      try { sock.destroy(); } catch { /* 忽略 */ }
      resolve(ok);
    };
    sock.setTimeout(timeoutMs);
    sock.once('connect', function () { finish(true); });
    sock.once('timeout', function () { finish(false); });
    sock.once('error', function () { finish(false); });
    sock.connect(port, '127.0.0.1');
  });
}

async function discoverUnblockPort(http, force) {
  if (neteaseUnblockPort) return neteaseUnblockPort;

  /* 启动路径与 unblock.status 可能同时触发。全段扫描要几秒，
   * 两个并发扫会互相抢连接、双双超时（实测 2.4s → 17.5s 且失败），
   * 所以共用同一个在飞的 promise。 */
  if (portProbeInFlight) return portProbeInFlight;

  const now = Date.now();
  // 失败越多等得越久（1s → 2s → 4s … 上限 60s），避免空转烧 CPU。
  const backoff = Math.min(1000 * Math.pow(2, portProbeFailures), 60000);
  if (!force && now - portProbeAt < backoff) return 0;
  portProbeAt = now;

  portProbeInFlight = (async function () {
    /* 只对 TCP 连得上的端口发 HTTP：开放端口通常只有几十个，
     * 逐个发 HTTP 也远快于对整段发。
     *
     * 识别请求**不带 unblock=true**：带了会触发上游解灰，
     * 冷启动实测 11s（同请求热了只要 2ms），会把扫描拖到超时；
     * 不带的实测 181–218ms，且照样能唯一区分 ——
     * 真后端返回 code=200 + data 数组，其它开放端口是 404/401。 */
    const identify = async function (port) {
      try {
        const r = await http.httpGet(
          'http://127.0.0.1:' + port + '/song/url/v1?id=186016&level=standard',
          { timeout: 3000 }
        );
        if (r.status !== 200 || !r.buf.length) return false;
        const j = JSON.parse(r.buf.toString('utf8'));
        return !!(j && j.code === 200 && Array.isArray(j.data));
      } catch {
        return false;
      }
    };

    const TCP_TIMEOUT = 250;
    const BATCH = 400;

    for (const [from, to] of EPHEMERAL_RANGES) {
      const ports = [];
      for (let p = from; p <= to; p++) ports.push(p);

      for (let i = 0; i < ports.length; i += BATCH) {
        const slice = ports.slice(i, i + BATCH);
        const tcp = await Promise.all(slice.map(function (p) { return tcpOpen(p, TCP_TIMEOUT); }));
        const open = slice.filter(function (_, k) { return tcp[k]; });
        if (!open.length) continue;

        const isUnblock = await Promise.all(open.map(identify));
        const found = open.filter(function (_, k) { return isUnblock[k]; });
        if (found.length) {
          neteaseUnblockPort = found[0];
          portProbeFailures = 0;
          urlCache.clear();
          return neteaseUnblockPort;
        }
      }
    }

    portProbeFailures++;
    return 0;
  })();

  try {
    return await portProbeInFlight;
  } finally {
    portProbeInFlight = null;
  }
}

/* 问解灰后端要一个可用 URL；返回 { url, kind } 或 null。
 * 超时必须给足：解灰链是「本地后端 → 上游解灰源 → 第三方 CDN」三段，
 * 实测 6s 会偶发 abort（同一个 URL 手测 0.9s 就回），放宽到 12s。 */
async function neteaseUnblockResolve(http, id) {
  if (!neteaseUnblockPort) return null;
  for (const level of UNBLOCK_LEVELS) {
    let j = null;
    try {
      j = await http.getJson(unblockUrl(id, level), { timeout: 12000 });
    } catch {
      continue;
    }
    const d = (j && j.data && j.data[0]) || null;
    const url = d && d.url;
    if (!url || !/^https?:/i.test(url)) continue;
    return { url: String(url), kind: d.type === 'flac' ? 'flac' : 'mp3' };
  }
  return null;
}

function buildDirectBackends(http) {
  /* ---- 聚合后端：搜索 + 无损取链，全平台走同一口子 ---- */
  /* 搜索用哪些 server、取链走哪个 server 是两件事：
   *
   *   netease 搜索结果里的 id 是网易云数字 id，且**只有 netease 这个 server 能把它
   *           换成真 FLAC**（同一个 id 交给 migu server 只回 MP3，实测 11.1MB vs 56MB）。
   *   migu    搜索返回的 id 与 netease **完全相同**（它是代理网易云数据），
   *           所以它只是个「备用搜索入口」，取链仍然要回 netease。
   *   kugou   返回的是 32 位 hash，跟数字 id 不通用，取链必须走 kugou；
   *           但实测 kugou 取链几乎全是空响应，只能当极低优先兜底。
   */
  function makeAgg(id, name, short, searchServers, urlServer, opts) {
    const officialFirst = !!(opts && opts.officialSearch);
    return {
      id: id,
      name: name,
      short: short,
      lossless: true,

      async search(q, limit, offset) {
        const seen = {};
        const out = [];

        const push = function (o) {
          const key = o.title + '\u0000' + o.artist;
          if (seen[key]) return;
          seen[key] = 1;
          out.push(o);
        };

        /* 路 0：原唱优先。版权曲目在 cloudsearch 里被降权到搜不到，
         * 但歌手全量歌曲接口不降权 —— 先把真原唱塞进来。 */
        if (officialFirst) {
          try {
            const orig = await neteaseArtistOriginals(http, q, limit);
            for (const r of orig) push(r);
          } catch {
            /* 忽略：不影响后面的常规搜索 */
          }
        }

        /* 路 1：网易云官方搜索。聚合站的 netease 搜索分支返空时，这是唯一能搜到的路。 */
        if (officialFirst) {
          try {
            const rows = await neteaseOfficialSearch(http, q, Math.max(10, limit));
            for (const r of rows) push(r);
          } catch {
            /* 落到聚合站 */
          }
        }

        for (const server of searchServers) {
          if (out.length >= limit) break;
          let j = null;
          try {
            j = await http.getJson(aggSearchUrl(q, server), {
              headers: { Referer: 'https://music.163.com/' },
            });
          } catch {
            continue;
          }
          if (!Array.isArray(j) || !j.length) continue;

          for (const it of j) {
            const sid = aggIdOf(it.url);
            if (!sid) continue;
            push({
              id: sid,
              title: it.name || '',
              artist: it.artist || '',
              album: '',
              cover: it.pic || '',
              durationMs: 0,
              _urlServer: server === 'kugou' ? 'kugou' : urlServer,
            });
          }
        }

        return out.slice(offset, offset + limit);
      },

      async url(song, quality) {
        const id = song.id;
        const server = song._urlServer || urlServer;
        const wantLossless = quality === 'lossless' || quality === 'hires';
        const chain = [];

        /* 优先级 -1：网易云解灰（Folia 自带后端）。
         * 这是**唯一**能拿到版权原唱完整版的路 —— 实测「晴天」原唱 269.75s，
         * 而聚合站对同一个 id 直接返空（0 字节）。
         * 它必须与主链**并发**跑，不能串在链前面 await：
         * 解灰链是「本地后端 → 上游解灰源 → 第三方 CDN」三段，实测 0.9~1.4s，
         * 串行会让每首歌都白等这一秒。并发时两边各跑各的，最后取更好的那个。
         * 端口自己探（见 discoverUnblockPort）；探到之前这一步静默跳过。 */
        const unblockPromise = /^\d+$/.test(String(id))
          ? (async function () {
              try {
                const port = neteaseUnblockPort || (await discoverUnblockPort(http));
                if (!port) return null;
                const ub = await neteaseUnblockResolve(http, id);
                if (!ub) return null;
                const p = await http.probe(ub.url, { Referer: 'https://music.163.com/' });
                if (!p || !p.ok) return null;
                return {
                  url: ub.url,
                  kind: p.kind,
                  via: 'unblock:netease:' + p.kind,
                  quality: isLosslessKind(p.kind) ? 'lossless' : (quality === 'standard' ? 'standard' : 'high'),
                  probe: p,
                };
              } catch {
                return null;
              }
            })()
          : Promise.resolve(null);

        // 优先级 0：br=740 = 无损档（实测真 FLAC 44.1k/24bit 起）。
        chain.push({ via: 'agg:' + server + ':740', url: meting(server, id, 740, AGG_HOST) });

        // 优先级 1：另一路 740（netease 拿不到时，migu/kugou 偶尔有）
        for (const s of ['netease', 'migu', 'kugou']) {
          if (s === server) continue;
          chain.push({ via: 'agg:' + s + ':740', url: meting(s, id, 740, AGG_HOST) });
        }

        // 优先级 2..：降级码率（有损兜底，保证「能播」）
        for (const br of METING_BR[quality] || METING_BR.lossless) {
          if (br === 740) continue;
          chain.push({ via: 'agg:' + server + ':' + br, url: meting(server, id, br, AGG_HOST) });
        }

        // 最后：163 官方外链（版权受限时常返回空，但便宜）
        chain.push({
          via: '163-outer',
          url: 'https://music.163.com/song/media/outer/url?id=' + id + '.mp3',
        });

        const mainPromise = resolveChain(http, chain, quality, { Referer: 'https://music.163.com/' });

        /* 解灰只等一个短预算：正常 0.9~1.4s 就回，但上游 CDN 挂掉时会拖到 12s 超时。
         * 给它 3.5s 窗口，超时就先用主链结果；主链也没结果时再回头把它的迟到值捞回来
         * （同一个 promise，不会多发请求）。 */
        let ub = null;
        try {
          ub = await Promise.race([
            unblockPromise,
            new Promise(function (r) { setTimeout(function () { r(null); }, 3500); }),
          ]);
        } catch {
          ub = null;
        }

        const main = await mainPromise;

        /* 主链没结果时，回头等一次解灰的迟到值。 */
        if (!main && !ub) {
          try { ub = await unblockPromise; } catch { ub = null; }
        }

        /* 取舍规则（顺序即优先级）：
         *   1. 主链给真无损 → 用主链。绝不用解灰的 320k MP3 换掉真 FLAC
         *      （实测「起风了」主链 110MB/88200Hz/24bit，解灰只有 10MB MP3）。
         *   2. 解灰给无损 → 用它（普通歌解灰也常回 FLAC）。
         *   3. 两边都是有损 → 用解灰：它给的是**原唱**，而聚合链对版权曲
         *      常常只能回同曲翻唱（实测《晴天》原唱 269s vs 翻唱 112s）。 */
        if (main && isLosslessKind(main.kind)) return main;
        if (ub && isLosslessKind(ub.kind)) return ub;
        return ub || main;
      },

      async lyric(song) {
        // 聚合接口自带 lrc 直链，优先用它
        try {
          const txt = await http.getText(
            'https://' + AGG_HOST + '/meting/?server=' + (song._urlServer || urlServer) +
              '&type=lrc&id=' + encodeURIComponent(song.id)
          );
          if (txt && /\[\d\d:\d\d/.test(txt)) return txt;
        } catch {
          /* 换官方 */
        }
        try {
          const j = await http.getJson(
            'https://music.163.com/api/song/lyric?id=' + song.id + '&lv=-1&kv=-1&tv=-1',
            { headers: { Referer: 'https://music.163.com/' } }
          );
          return (j && j.lrc && j.lrc.lyric) || null;
        } catch {
          return null;
        }
      },
    };
  }

  /* wy 的搜索三级兜底：官方直连 → 聚合 netease → 聚合 migu（migu 返回的就是网易云 id，
   * 所以取链仍走 netease）。2026-10-16 起聚合 netease 搜索返空，官方直连顶上主路。 */
  const wy = makeAgg('wy', '网易云（聚合）', '网', ['netease', 'migu'], 'netease', { officialSearch: true });
  const migu = makeAgg('migu', '咪咕（聚合）', '咪', ['migu', 'netease'], 'netease');
  const kugou = makeAgg('kugou', '酷狗（聚合）', '酷', ['kugou'], 'kugou');

  return [wy, migu, kugou];
}

/* ══════════════════════════════════════════════════════════════════
 * 跨平台回退：拿歌名+歌手去网易云重匹配
 * ══════════════════════════════════════════════════════════════════ */

function normText(s) {
  return String(s || '')
    .toLowerCase()
    .replace(/[\s\-_()（）[\]【】·,，.。!！?？'"'"]/g, '');
}

/* 按相关度排序（不是只取一个）：标题完全相同 > 标题包含 > 只有歌手相同。
 * 返回全部候选，按分数从高到低。取链时逐个试，避免「第一条恰好没资源」就整首失败。 */
function rankSongs(target, list) {
  const tTitle = normText(target.title);
  const tArtist = normText(target.artist);

  const scored = list.map(function (it) {
    let sc = 0;
    const iTitle = normText(it.title);
    const iArtist = normText(it.artist);

    if (iTitle && tTitle) {
      if (iTitle === tTitle) sc += 100;
      else if (iTitle.indexOf(tTitle) >= 0 || tTitle.indexOf(iTitle) >= 0) sc += 55;
    }
    if (tArtist && iArtist) {
      if (iArtist.indexOf(tArtist) >= 0 || tArtist.indexOf(iArtist) >= 0) sc += 40;
      else {
        const a1 = tArtist.split(/[/、,&]/)[0];
        const a2 = iArtist.split(/[/、,&]/)[0];
        if (a1 && a2 && (a1.indexOf(a2) >= 0 || a2.indexOf(a1) >= 0)) sc += 20;
      }
    }
    return { it: it, sc: sc };
  });

  scored.sort(function (a, b) { return b.sc - a.sc; });
  return scored.map(function (x) { return x.it; });
}

function pickBestSong(target, list) {
  const ranked = rankSongs(target, list);
  if (!ranked.length) return null;

  const tTitle = normText(target.title);
  const tArtist = normText(target.artist);
  const first = ranked[0];
  const iTitle = normText(first.title);
  const iArtist = normText(first.artist);

  let sc = 0;
  if (iTitle && tTitle) {
    if (iTitle === tTitle) sc += 100;
    else if (iTitle.indexOf(tTitle) >= 0 || tTitle.indexOf(iTitle) >= 0) sc += 55;
  }
  if (tArtist && iArtist) {
    if (iArtist.indexOf(tArtist) >= 0 || tArtist.indexOf(iArtist) >= 0) sc += 40;
  }
  return sc >= 40 ? first : null;
}

/* ══════════════════════════════════════════════════════════════════
 * B. 洛雪脚本宿主
 * ══════════════════════════════════════════════════════════════════ */

function createLxRequest(fetchImpl) {
  return function lxRequest(url, options, callback) {
    if (typeof options === 'function') {
      callback = options;
      options = {};
    }
    options = options || {};
    if (typeof callback !== 'function') return;

    const method = String(options.method || 'GET').toUpperCase();
    const headers = Object.assign({ 'User-Agent': UA_OKHTTP }, options.headers || {});
    let body = options.body;

    if (options.form && body === undefined) {
      headers['Content-Type'] = headers['Content-Type'] || 'application/x-www-form-urlencoded';
      body = new URLSearchParams(options.form).toString();
    } else if (options.json !== undefined && body === undefined) {
      headers['Content-Type'] = headers['Content-Type'] || 'application/json';
      body = JSON.stringify(options.json);
    } else if (body && typeof body === 'object' && !Buffer.isBuffer(body)) {
      headers['Content-Type'] = headers['Content-Type'] || 'application/json';
      body = JSON.stringify(body);
    }

    const timeoutMs = Number(options.timeout) > 0 ? Number(options.timeout) : ACTION_TIMEOUT_MS;
    const controller = new AbortController();
    const timer = setTimeout(function () {
      controller.abort();
    }, timeoutMs);

    fetchImpl(url, {
      method: method,
      headers: headers,
      body: body,
      redirect: 'follow',
      signal: controller.signal,
    })
      .then(async function (res) {
        const text = await res.text();
        let parsed = text;
        try {
          parsed = JSON.parse(text);
        } catch {
          /* 保持字符串，洛雪也是这样 */
        }
        const outHeaders = {};
        res.headers.forEach(function (v, k) {
          outHeaders[k] = v;
        });
        callback(null, {
          statusCode: res.status,
          statusMessage: res.statusText,
          headers: outHeaders,
          body: parsed,
          raw: text,
        });
      })
      .catch(function (err) {
        callback(err);
      })
      .finally(function () {
        clearTimeout(timer);
      });
  };
}

function createLxRuntime(script, label, fetchImpl) {
  const state = { handler: null, info: null };
  let finishInit;
  let failInit;
  const initialized = new Promise(function (resolve, reject) {
    finishInit = resolve;
    failInit = reject;
  });
  // 调用方可能提前返回（脚本执行就失败），先挂一个空处理器防止未处理拒绝。
  initialized.catch(function () {});

  const lxRequest = createLxRequest(fetchImpl);

  const lx = {
    EVENT_NAMES: EVENT_NAMES,
    request: lxRequest,
    on(eventName, handler) {
      if (eventName === EVENT_NAMES.request && typeof handler === 'function') state.handler = handler;
      return Promise.resolve();
    },
    send(eventName, data) {
      if (eventName === EVENT_NAMES.inited) {
        state.info = data || {};
        finishInit(state.info);
      }
      return Promise.resolve();
    },
    utils: {
      request: lxRequest,
      fetch: lxRequest,
      httpFetch: lxRequest,
      crypto: crypto.webcrypto,
      buffer: {
        from: function () {
          return Buffer.from.apply(Buffer, arguments);
        },
        bufToString: function (buf, format) {
          return Buffer.from(buf, 'binary').toString(format);
        },
      },
      zlib: {
        inflate: function (data) {
          return new Promise(function (resolve, reject) {
            zlib.inflate(data, function (e, b) {
              return e ? reject(e) : resolve(b);
            });
          });
        },
        deflate: function (data) {
          return new Promise(function (resolve, reject) {
            zlib.deflate(data, function (e, b) {
              return e ? reject(e) : resolve(b);
            });
          });
        },
      },
    },
    currentScriptInfo: {
      name: label,
      description: '',
      version: '',
      author: '',
      homepage: '',
      rawScript: script,
    },
    version: '2.0.0',
    env: 'desktop',
  };

  const quiet = {
    log: function () {},
    info: function () {},
    warn: function () {},
    error: function () {},
    debug: function () {},
  };

  const sandbox = {
    lx: lx,
    console: quiet,
    Buffer: Buffer,
    process: { platform: process.platform, versions: process.versions, env: {} },
    URL: URL,
    URLSearchParams: URLSearchParams,
    TextEncoder: TextEncoder,
    TextDecoder: TextDecoder,
    AbortController: AbortController,
    fetch: fetchImpl,
    crypto: crypto.webcrypto,
    setTimeout: setTimeout,
    clearTimeout: clearTimeout,
    setInterval: setInterval,
    clearInterval: clearInterval,
    queueMicrotask: queueMicrotask,
    atob: function (v) {
      return Buffer.from(String(v), 'base64').toString('binary');
    },
    btoa: function (v) {
      return Buffer.from(String(v), 'binary').toString('base64');
    },
  };
  sandbox.globalThis = sandbox;
  sandbox.global = sandbox;
  sandbox.window = sandbox;
  sandbox.self = sandbox;

  try {
    vm.runInNewContext(script, sandbox, {
      filename: 'lx-source-' + label + '.js',
      timeout: 15000,
      displayErrors: true,
    });
  } catch (err) {
    failInit(err);
    return { initFailed: err };
  }

  return {
    initialized: withTimeout(initialized, INIT_TIMEOUT_MS, 'LX_SOURCE_INIT_TIMEOUT'),
    get sources() {
      return (state.info && state.info.sources) || {};
    },
    get hasHandler() {
      return typeof state.handler === 'function';
    },
    request(source, action, info) {
      if (typeof state.handler !== 'function') throw new Error('LX_SOURCE_REQUEST_HANDLER_MISSING');
      return withTimeout(
        Promise.resolve(state.handler({ source: source, action: action, info: info })),
        ACTION_TIMEOUT_MS,
        'LX_ACTION_TIMEOUT'
      );
    },
  };
}

/* ══════════════════════════════════════════════════════════════════
 * 音源注册表
 * ══════════════════════════════════════════════════════════════════ */

class SourceRegistry {
  constructor(api, http) {
    this.api = api;
    this.http = http;
    this.direct = buildDirectBackends(http);
    this.lxUnits = [];
    this.songCache = new Map();
    this.nextSeq = 1;
    this.disabled = new Set();
    this.config = Object.assign({}, DEFAULT_CONFIG);
    this.storage = this._openStorage();
  }

  /* ---- 持久化 ---- */

  _openStorage() {
    const file = path.join(__dirname, 'state.json');
    const fallback = {
      async get(k) {
        try {
          const all = JSON.parse(fs.readFileSync(file, 'utf8'));
          return all[k];
        } catch {
          return undefined;
        }
      },
      async set(k, v) {
        let all = {};
        try {
          all = JSON.parse(fs.readFileSync(file, 'utf8'));
        } catch {
          all = {};
        }
        all[k] = v;
        fs.writeFileSync(file, JSON.stringify(all, null, 2), 'utf8');
      },
    };
    try {
      const s = this.api.storage && this.api.storage.data;
      if (s && typeof s.get === 'function' && typeof s.set === 'function') return s;
    } catch {
      /* 用文件兜底 */
    }
    return fallback;
  }

  async loadState() {
    try {
      const cfg = await this.storage.get(CONFIG_KEY);
      if (cfg && typeof cfg === 'object') this.config = Object.assign({}, DEFAULT_CONFIG, cfg);
    } catch {
      /* 忽略 */
    }
    try {
      const dis = await this.storage.get(DISABLED_KEY);
      if (Array.isArray(dis)) this.disabled = new Set(dis.map(String));
    } catch {
      /* 忽略 */
    }
  }

  async saveDisabled() {
    try {
      await this.storage.set(DISABLED_KEY, Array.from(this.disabled));
    } catch (err) {
      this.api.log.warn('保存启用状态失败', String(err));
    }
  }

  async saveConfig() {
    try {
      await this.storage.set(CONFIG_KEY, this.config);
    } catch (err) {
      this.api.log.warn('保存配置失败', String(err));
    }
  }

  /* ---- 扫描脚本 ---- */

  /*
   * 音源目录必须放在模组目录**之外**。
   *
   * 原因：宿主把「启用本模组」的授权绑定到模组目录整棵树的哈希
   * （electron/modSystem/modDigest.cjs 的 computeModDigest 会遍历每个文件，
   * 路径与内容都进哈希）。音源文件一旦落在模组目录内，用户每添加或删除一个音源，
   * 模组哈希就变化，宿主的 resolveTrust 会当场判定 trustStale 并把模组停用 ——
   * 表现为「加一个音源，整个模组失效，要重新点一次『仍要启用』」。
   *
   * 放到 userData 下同时解决两件事：躲开哈希，以及不把有版权的音源混进发布包。
   *
   * __dirname = <userData>/mods/<modId>，所以上跳两级就是 <userData>。
   */
  sourcesDir() {
    if (this._sourcesDir) return this._sourcesDir;

    let external = null;
    try {
      external = path.join(path.dirname(path.dirname(__dirname)), 'lx-music-sources');
      fs.mkdirSync(external, { recursive: true });
      fs.accessSync(external, fs.constants.W_OK);
    } catch {
      // 只读环境（例如模组被放进 resources/mods/）回退到模组内目录，
      // 此时用户仍能读已有音源，只是新增会失败并给出明确报错。
      external = path.join(__dirname, 'sources');
    }

    this._sourcesDir = external;
    return external;
  }

  ensureDir() {
    try {
      fs.mkdirSync(this.sourcesDir(), { recursive: true });
    } catch {
      /* 已存在 */
    }
    this.migrateLegacySources();
  }

  /*
   * 老版本把音源放在模组目录内的 sources/。那个位置会污染模组哈希，
   * 所以首次运行时搬一次家，并清掉模组内的旧目录（连同 .gitkeep 之类）。
   * 只搬 .js，且目标已存在同名文件时不覆盖。
   */
  migrateLegacySources() {
    if (this._migrated) return;
    this._migrated = true;

    const legacy = path.join(__dirname, 'sources');
    const target = this.sourcesDir();
    if (path.resolve(legacy) === path.resolve(target)) return;

    let moved = 0;
    try {
      if (fs.existsSync(legacy)) {
        for (const f of fs.readdirSync(legacy)) {
          if (!f.toLowerCase().endsWith('.js')) continue;
          const src = path.join(legacy, f);
          const dst = path.join(target, f);
          if (fs.existsSync(dst)) continue;
          try {
            fs.copyFileSync(src, dst);
            moved++;
          } catch (err) {
            this.api.log.warn('迁移音源失败 ' + f, String(err));
          }
        }
        // 整个旧目录都要消失：留在模组树里会继续参与哈希。
        fs.rmSync(legacy, { recursive: true, force: true });
      }
    } catch (err) {
      this.api.log.warn('清理模组内旧 sources/ 失败', String(err));
    }

    if (moved) {
      this.api.log.info('已把 ' + moved + ' 个音源迁到 ' + target + '（原位置会破坏模组信任）');
    }
  }

  async loadScripts() {
    this.lxUnits = [];
    this.ensureDir();

    let files = [];
    try {
      files = fs.readdirSync(this.sourcesDir()).filter(function (f) {
        return f.toLowerCase().endsWith('.js');
      });
    } catch {
      this.api.log.warn('sources/ 目录不存在或不可读');
      return;
    }

    for (const file of files) {
      const full = path.join(this.sourcesDir(), file);
      const name = path.basename(file, '.js');
      const uid = 'lx:' + name;

      let script;
      try {
        script = fs.readFileSync(full, 'utf8');
      } catch (err) {
        this.lxUnits.push({
          id: uid, name: name, short: name.slice(0, 2), kind: 'lx', file: full,
          ok: false, error: '读取失败: ' + err.message,
        });
        continue;
      }

      const runtime = createLxRuntime(script, name, this.http.fetchImpl);
      if (runtime.initFailed) {
        this.lxUnits.push({
          id: uid, name: name, short: name.slice(0, 2), kind: 'lx', file: full,
          ok: false, error: '执行失败: ' + runtime.initFailed.message,
        });
        continue;
      }

      try {
        await runtime.initialized;
      } catch (err) {
        this.lxUnits.push({
          id: uid, name: name, short: name.slice(0, 2), kind: 'lx', file: full,
          ok: false, error: '初始化失败: ' + err.message,
        });
        continue;
      }

      const sources = runtime.sources || {};
      const keys = Object.keys(sources);
      if (!runtime.hasHandler || keys.length === 0) {
        this.lxUnits.push({
          id: uid, name: name, short: name.slice(0, 2), kind: 'lx', file: full,
          ok: false, error: '没有声明任何音源',
        });
        continue;
      }

      let lossless = false;
      try {
        lossless = JSON.stringify(sources).toLowerCase().indexOf('flac') >= 0;
      } catch {
        lossless = false;
      }

      // 只有声明了 musicSearch 的平台才能当搜索源
      const searchable = keys.filter(function (k) {
        const acts = ((sources[k] && sources[k].actions) || []).map(function (a) {
          return String(a).replace(/^music/i, '').toLowerCase();
        });
        return acts.indexOf('search') >= 0;
      });

      this.lxUnits.push({
        id: uid, name: name, short: name.slice(0, 2), kind: 'lx', file: full,
        ok: true, runtime: runtime, sources: sources, keys: keys,
        searchable: searchable, lossless: lossless,
      });

      this.api.log.info(
        '已加载音源脚本「' + name + '」',
        '平台 ' + keys.join('/') + (searchable.length ? '，可搜索 ' + searchable.join('/') : '，仅取链')
      );
    }
  }

  /* ---- 统一清单 ---- */

  units() {
    const self = this;
    const direct = this.direct.map(function (b) {
      return {
        id: b.id, name: b.name, short: b.short, kind: 'direct',
        slug: b.id, ok: true, searchable: true, lossless: !!b.lossless,
      };
    });
    const lx = this.lxUnits.map(function (u) {
      return {
        id: u.id, name: u.name, short: u.short, kind: 'lx', slug: u.name,
        ok: u.ok, error: u.error || null,
        searchable: !!(u.searchable && u.searchable.length),
        lossless: !!u.lossless,
      };
    });
    return direct.concat(lx).map(function (u) {
      u.enabled = self.isEnabled(u.id);
      return u;
    });
  }

  isEnabled(id) {
    const list = String(this.config.enabledSources || '').trim();
    if (list) {
      const allow = list.split(/[,，\s]+/).filter(Boolean);
      if (allow.length) return allow.indexOf(id) >= 0;
    }
    return !this.disabled.has(id);
  }

  findUnit(id) {
    const b = this.direct.find(function (x) { return x.id === id; });
    if (b) return { id: b.id, name: b.name, short: b.short, kind: 'direct', backend: b };
    const u = this.lxUnits.find(function (x) { return x.id === id; });
    if (u) return Object.assign({}, u, { kind: 'lx' });
    return null;
  }

  /* ---- 歌曲 id 编解码 ---- */

  encodeSong(unitId, song) {
    const sid =
      song.songmid != null ? song.songmid
      : song.id != null ? song.id
      : song.songId != null ? song.songId
      : song.rid != null ? song.rid
      : song.hash != null ? song.hash
      : '';
    const id = unitId + '|' + sid;
    this.songCache.set(id, song);
    if (this.songCache.size > 2000) {
      const first = this.songCache.keys().next().value;
      this.songCache.delete(first);
    }
    return id;
  }

  decodeSong(id) {
    const s = String(id);
    const idx = s.lastIndexOf('|');
    if (idx < 0) return null;
    const unitId = s.slice(0, idx);
    const sid = s.slice(idx + 1);
    const cached = this.songCache.get(s);
    return { unitId: unitId, sid: sid, song: cached || { id: sid, songmid: sid, name: '', singer: '' } };
  }

  /* ---- search ---- */

  async search(unitId, keyword, limit, offset) {
    const unit = this.findUnit(unitId);
    if (!unit) throw new Error('未知音源：' + unitId);
    if (!this.isEnabled(unitId)) throw new Error('音源已停用：' + unit.name);

    const q = String(keyword == null ? '' : keyword).trim();
    if (!q) return { items: [], hasMore: false };
    const lim = Math.max(1, Math.min(50, Number(limit) || 30));
    const off = Math.max(0, Number(offset) || 0);

    let raw = [];

    if (unit.kind === 'direct') {
      raw = await unit.backend.search(q, lim, off);
    } else {
      const target = (unit.searchable || [])[0];

      // 脚本声明的搜索平台可能已经失效（比如 qsvip 接口 404）。
      // 先试脚本自己的；失败或空结果就退回网易云搜索，再交给脚本取链。
      if (target) {
        try {
          const page = Math.floor(off / lim) + 1;
          const res = await unit.runtime.request(target, 'musicSearch', {
            keyword: q, page: page, pagesize: lim, limit: lim,
          });
          const list = Array.isArray(res) ? res : (res && (res.list || res.data)) || [];
          raw = list.map(function (s) {
            return {
              id: String(
                s.songmid != null ? s.songmid
                : s.id != null ? s.id
                : s.songId != null ? s.songId
                : s.rid != null ? s.rid
                : s.hash != null ? s.hash
                : ''
              ),
              title: String(s.name || s.title || ''),
              artist: s.singer
                ? String(s.singer).split(/[、,&/]/).map(function (x) { return x.trim(); }).filter(Boolean).join(' / ')
                : '',
              album: s.albumName || '',
              cover: s.img || '',
              durationMs: (Number(s.interval) || 0) * 1000,
              _raw: s,
            };
          });
        } catch (err) {
          this.api.log.warn(
            '音源「' + unit.name + '」自带搜索失败，改用网易云搜索',
            String((err && err.message) || err)
          );
          raw = [];
        }
      }

      if (!raw.length) {
        const wy = this.direct[0];
        const hits = await wy.search(q, lim, off);
        // 标记 source=wy，取链时脚本才知道该走哪个平台。
        raw = hits.map(function (s) {
          return Object.assign({}, s, { _raw: Object.assign({ source: 'wy' }, s) });
        });
      }
    }

    const self = this;
    const items = raw
      .filter(function (s) { return !!s.id; })
      .slice(0, lim)
      .map(function (s) {
        const item = {
          id: self.encodeSong(unitId, s._raw || s),
          title: s.title || '未知歌曲',
          artists: s.artist
            ? String(s.artist).split(/[、,&/]/).map(function (x) { return x.trim(); }).filter(Boolean)
            : [],
        };
        if (!item.artists.length) item.artists = ['未知歌手'];
        if (s.album) item.album = String(s.album);
        if (s.cover) item.coverUrl = String(s.cover);
        if (Number.isFinite(s.durationMs) && s.durationMs > 0) item.durationMs = s.durationMs;
        return item;
      });

    return { items: items, hasMore: raw.length >= lim };
  }

  /* ---- getSong ---- */

  async getSong(unitId, songId) {
    const decoded = this.decodeSong(songId);
    if (!decoded) return null;
    const s = decoded.song;
    return {
      id: songId,
      title: s.title || s.name || '未知歌曲',
      artists: s.artist ? String(s.artist).split(/[、,&/]/).filter(Boolean) : ['未知歌手'],
      album: s.album || undefined,
      coverUrl: s.cover || undefined,
      durationMs: Number(s.durationMs) || undefined,
    };
  }

  /* ---- getAudioUrl ---- */

  async getAudioUrl(unitId, songId, quality) {
    const unit = this.findUnit(unitId);
    if (!unit) throw new Error('未知音源：' + unitId);

    const decoded = this.decodeSong(songId);
    if (!decoded) throw new Error('无效的歌曲 id');

    const q = normQuality(quality || this.config.quality);
    const wantLossless = q === 'lossless' || q === 'hires';

    // 命中缓存直接返回（只缓存探测通过的 URL，TTL 20 分钟）
    const ck = cacheKey(unitId, songId, q);
    const cached = cacheGet(ck);
    if (cached) {
      if (!wantLossless || cached.quality === 'lossless') return cached;
    }

    let hit = null;
    let lastErr = null;

    if (unit.kind === 'direct') {
      try {
        hit = await unit.backend.url(decoded.song, q);
      } catch (err) {
        lastErr = err;
      }

      // 本后端没拿到（或只拿到有损）：让其他直连后端也试同一个 id。
      // 实测 netease 拿不到时 migu/kugou 偶尔有，成本只有 1 次请求。
      if (!hit || (wantLossless && hit.quality !== 'lossless')) {
        for (const other of this.direct) {
          if (other === unit.backend) continue;
          let alt = null;
          try {
            alt = await other.url(decoded.song, q);
          } catch {
            continue;
          }
          if (!alt) continue;
          if (!hit) hit = alt;
          if (!wantLossless || alt.quality === 'lossless') {
            if (alt.quality === 'lossless') hit = alt;
            break;
          }
        }
      }
    } else {
      // 脚本音源走的是脚本内部的慢速重试（实测 6~32s），而内置直连链 300ms 内就能拿到
      // 真 FLAC。所以：如果这首歌本来就是从网易云搜来的（source=wy），先试直连链。
      if (decoded.song && decoded.song.source === 'wy') {
        try {
          hit = await this.direct[0].url(decoded.song, q);
        } catch {
          hit = null;
        }
      }

      // 直连链没拿到无损，再交给脚本
      if (!hit || (wantLossless && hit.quality !== 'lossless')) {
        try {
          const lxHit = await this._lxUrl(unit, decoded.song, q);
          if (lxHit && (!hit || (wantLossless && lxHit.quality === 'lossless'))) hit = lxHit;
        } catch (err) {
          lastErr = err;
        }
      }
    }

    // 跨平台回退：拿歌名+歌手去重新搜索匹配。
    //
    // 两种情况必须回退：
    //   1) 一个候选都没拿到（!hit）—— 不回退就是整首不能播，代价再高也得试；
    //   2) 要无损却只拿到有损，且这首歌的 id 是酷狗那种 32 位 hash ——
    //      数字 id 是网易云体系，重搜只会拿到同一首、同样结果，纯属白等。
    const sid = String((decoded.song && decoded.song.id) || '');
    const hashLike = !!sid && !/^\d+$/.test(sid);

    const needFallback =
      this.config.fallback !== false &&
      (!hit || (hashLike && wantLossless && hit.quality !== 'lossless'));

    if (needFallback) {
      try {
        const fb = await this._crossFallback(decoded.song, q);
        if (fb && (!hit || (wantLossless && fb.quality === 'lossless'))) hit = fb;
      } catch {
        /* 回退失败就用原结果 */
      }
    }

    if (!hit) throw lastErr || new Error('所有候选都取链失败');

    const out = { url: hit.url, quality: hit.quality, via: hit.via, kind: hit.kind };
    if (hit.probe) {
      if (hit.probe.bits) out.bitsPerSample = hit.probe.bits;
      if (hit.probe.sampleRate) out.sampleRate = hit.probe.sampleRate;
      if (hit.probe.bytes) out.bytes = hit.probe.bytes;
    }

    // 只缓存探测通过的可用结果
    cacheSet(ck, out);
    return out;
  }

  async _lxUrl(unit, song, quality) {
    const chain = LX_LEVEL[quality] || LX_LEVEL.lossless;

    // 脚本返回的原始 song 带 source 字段 —— 用它精确路由到对应平台，
    // 不要把同一个 musicInfo 轮询投给所有平台（会拿到别的平台的错误结果）。
    const preferred = song && song.source;
    const platforms = preferred && unit.keys.indexOf(preferred) >= 0 ? [preferred] : unit.keys;

    for (const type of chain) {
      for (const platform of platforms) {
        const acts = ((unit.sources[platform] && unit.sources[platform].actions) || []).map(function (a) {
          return String(a).replace(/^music/i, '').toLowerCase();
        });
        if (acts.indexOf('url') < 0) continue;
        try {
          const url = await unit.runtime.request(platform, 'musicUrl', { type: type, musicInfo: song });
          if (typeof url === 'string' && /^https?:/i.test(url)) {
            const p = await this.http.probe(url);
            if (p.ok) {
              return {
                url: url,
                kind: p.kind,
                via: unit.name + '/' + platform + '/' + type,
                quality: isLosslessKind(p.kind) ? 'lossless' : quality === 'standard' ? 'standard' : 'high',
                probe: p,
              };
            }
            return {
              url: url,
              kind: 'unknown',
              via: unit.name + '/' + platform + '/' + type,
              quality: quality === 'standard' ? 'standard' : 'high',
            };
          }
        } catch {
          /* 换下一个 */
        }
      }
    }
    return null;
  }

  /* 跨平台回退：拿歌名+歌手去网易云重匹配。
   *
   * 只在「一个候选都没拿到」或「要无损却只拿到有损」时才走。
   * 遍历所有直连后端（不止第一个），任何一个给出无损就立刻收工。
   * 最后再拿**全部候选里最好的那个**（有损也要），保证「能播」优先于「无损」。 */
  async _crossFallback(song, quality) {
    const title = song.title || song.name || '';
    const artist = song.artist || song.singer || '';
    const q = [title, artist].filter(Boolean).join(' ').trim();
    if (!q) return null;

    const wantLossless = quality === 'lossless' || quality === 'hires';

    // 先把所有后端 × 所有候选的结果收集起来，再分两轮判定。
    // 不能边搜边返回：酷狗往往排在网易云前面，它给出 9MB 的 mp3 时如果直接收工，
    // 就会漏掉网易云同一首歌的 20MB 真 FLAC。
    const cands = [];
    for (const backend of this.direct) {
      let hits = [];
      try {
        hits = await backend.search(q, 20, 0);
      } catch {
        continue;
      }
      if (!hits.length) continue;
      for (const it of rankSongs({ title: title, artist: artist }, hits).slice(0, 8)) {
        cands.push({ backend: backend, it: it });
      }
    }
    if (!cands.length) return null;

    let best = null;
    for (const c of cands) {
      let hit = null;
      try {
        hit = await c.backend.url(c.it, quality);
      } catch {
        continue;
      }
      if (!hit) continue;
      if (wantLossless && hit.quality === 'lossless') {
        hit.via = hit.via + '(回退)';
        return hit;
      }
      if (!best) best = hit;
    }

    if (best) best.via = best.via + '(回退)';
    return best;
  }

  /* ---- getLyrics ---- */

  async getLyrics(unitId, songId) {
    const unit = this.findUnit(unitId);
    const decoded = this.decodeSong(songId);
    if (!decoded) return null;

    if (unit && unit.kind === 'direct') {
      try {
        return await unit.backend.lyric(decoded.song);
      } catch {
        return null;
      }
    }

    if (unit && unit.kind === 'lx') {
      for (const platform of unit.keys) {
        const acts = ((unit.sources[platform] && unit.sources[platform].actions) || []).map(function (a) {
          return String(a).replace(/^music/i, '').toLowerCase();
        });
        if (acts.indexOf('lyric') < 0) continue;
        try {
          const res = await unit.runtime.request(platform, 'lyric', { musicInfo: decoded.song });
          const text =
            typeof res === 'string' ? res : (res && (res.lyric || res.lrc || (res.data && res.data.lyric))) || '';
          if (text && String(text).trim()) return String(text);
        } catch {
          /* 换下一个 */
        }
      }
    }

    // 兜底：直接问网易云
    try {
      const wy = this.direct[0];
      if (!wy) return null;
      const q = [decoded.song.title || decoded.song.name, decoded.song.artist || decoded.song.singer]
        .filter(Boolean)
        .join(' ');
      if (!q) return null;
      const hits = await wy.search(q, 5, 0);
      const best = pickBestSong(
        { title: decoded.song.title || decoded.song.name, artist: decoded.song.artist || decoded.song.singer },
        hits
      );
      if (!best) return null;
      return wy.lyric(best);
    } catch {
      return null;
    }
  }

  /* ---- 增删改 ---- */

  async toggle(id, enabled) {
    const unit = this.findUnit(id);
    if (!unit) return { ok: false, error: '未知音源' };
    this.config.enabledSources = '';
    if (enabled) this.disabled.delete(id);
    else this.disabled.add(id);
    await this.saveDisabled();
    await this.saveConfig();
    return { ok: true, name: unit.name };
  }

  async addSource(target, name) {
    this.ensureDir();
    const t = String(target || '').trim();
    if (!t) return { ok: false, error: '空的目标' };

    let script = null;
    let baseName = name || null;

    if (/^https?:\/\//i.test(t)) {
      try {
        const r = await this.http.httpGet(t, { timeout: 30000 });
        if (r.status >= 400) return { ok: false, error: '下载失败 HTTP ' + r.status };
        script = r.buf.toString('utf8');
        if (!baseName) {
          const u = new URL(t);
          baseName = decodeURIComponent(path.basename(u.pathname) || 'source').replace(/\.js$/i, '');
        }
      } catch (err) {
        return { ok: false, error: '下载失败：' + String((err && err.message) || err) };
      }
    } else {
      const p = t.replace(/^"|"$/g, '');
      if (!fs.existsSync(p)) return { ok: false, error: '文件不存在：' + p };
      try {
        script = fs.readFileSync(p, 'utf8');
      } catch (err) {
        return { ok: false, error: '读取失败：' + String((err && err.message) || err) };
      }
      if (!baseName) baseName = path.basename(p, '.js');
    }

    const safe = String(baseName).replace(/[\\/:*?"<>|]/g, '_').slice(0, 64) || 'source-' + this.nextSeq++;
    const dest = path.join(this.sourcesDir(), safe + '.js');

    const warnings = [];
    if (fs.existsSync(dest)) warnings.push('已存在同名脚本，已覆盖：' + safe + '.js');
    try {
      fs.writeFileSync(dest, script, 'utf8');
    } catch (err) {
      return { ok: false, error: '写入失败：' + String((err && err.message) || err) };
    }

    await this.loadScripts();
    const unit = this.lxUnits.find(function (u) { return u.id === 'lx:' + safe; });
    if (!unit) return { ok: false, error: '写入成功但未能加载' };
    if (!unit.ok) warnings.push('脚本加载失败：' + unit.error);
    else {
      this.disabled.delete(unit.id);
      await this.saveDisabled();
    }

    return { ok: true, name: safe, file: dest, warnings: warnings };
  }

  async removeSource(id) {
    const unit = this.lxUnits.find(function (u) { return u.id === id; });
    if (!unit) {
      if (this.direct.some(function (b) { return b.id === id; })) {
        return { ok: false, error: '内置音源不能删除，请用「停用音源」' };
      }
      return { ok: false, error: '未知音源（只有脚本音源可删除）' };
    }
    try {
      fs.unlinkSync(unit.file);
    } catch (err) {
      return { ok: false, error: '删除失败：' + String((err && err.message) || err) };
    }
    this.disabled.delete(id);
    await this.saveDisabled();
    await this.loadScripts();
    return { ok: true, name: unit.name };
  }

  async reload() {
    await this.loadState();
    await this.loadScripts();
    return { units: this.units() };
  }

  status() {
    const units = this.units();
    return {
      units: units,
      enabled: units.filter(function (u) { return u.enabled && u.ok !== false; }).length,
      total: units.length,
      quality: this.config.quality,
      fallback: this.config.fallback !== false,
    };
  }
}

/* ══════════════════════════════════════════════════════════════════
 * 入口
 * ══════════════════════════════════════════════════════════════════ */

module.exports = function activate(api) {
  installRejectionGuard(api);

  const fetchImpl = typeof globalThis.fetch === 'function' ? globalThis.fetch.bind(globalThis) : null;

  if (!fetchImpl) {
    api.log.error('当前环境没有 fetch，音源无法工作');
    return function () {};
  }

  const http = makeHttp(fetchImpl);
  const reg = new SourceRegistry(api, http);

  // 首次加载完成前，RPC 先等一下，否则 client 拉到的清单里会缺洛雪脚本。
  const ready = (async function () {
    await reg.loadState();
    await reg.loadScripts();
  })();

  function whenReady(fn) {
    return async function () {
      try {
        await withTimeout(ready, 45000, 'SOURCE_READY_TIMEOUT');
      } catch {
        /* 超时就按当前已加载的清单返回 */
      }
      return fn.apply(null, arguments);
    };
  }

  api.rpc.handle('sources.list', whenReady(async function () {
    return { units: reg.units() };
  }));
  api.rpc.handle('sources.toggle', async function (id, enabled) {
    return reg.toggle(String(id), !!enabled);
  });
  api.rpc.handle('sources.add', async function (target, name) {
    return reg.addSource(target, name);
  });
  api.rpc.handle('sources.remove', async function (id) {
    return reg.removeSource(String(id));
  });
  api.rpc.handle('sources.reload', async function () {
    return reg.reload();
  });
  api.rpc.handle('sources.status', whenReady(async function () {
    return reg.status();
  }));

  api.rpc.handle('source.search', async function (unitId, kw, limit, offset) {
    return reg.search(String(unitId), kw, Number(limit) || 30, Number(offset) || 0);
  });
  api.rpc.handle('source.song', async function (unitId, songId) {
    return reg.getSong(String(unitId), String(songId));
  });
  api.rpc.handle('source.url', async function (unitId, songId, quality) {
    return reg.getAudioUrl(String(unitId), String(songId), quality);
  });
  api.rpc.handle('source.lyric', async function (unitId, songId) {
    return reg.getLyrics(String(unitId), String(songId));
  });

  api.rpc.handle('config.sync', async function (values) {
    if (values && typeof values === 'object') {
      if (values.quality) reg.config.quality = normQuality(values.quality);
      if (typeof values.fallback === 'boolean') reg.config.fallback = values.fallback;
      if (typeof values.enabledSources === 'string') reg.config.enabledSources = values.enabledSources;
      /* 端口仍然接受渲染层上报（某些布局下 client 能看到 electron）。
       * 但**不依赖它** —— 模组 client 跑在隔离上下文时 window.electron 是 undefined，
       * 主进程会自己探（discoverUnblockPort）。 */
      const p = Number(values.unblockPort);
      if (Number.isInteger(p) && p > 0 && p < 65536 && p !== neteaseUnblockPort) {
        const first = !neteaseUnblockPort;
        neteaseUnblockPort = p;
        if (first) urlCache.clear();
        api.log.info('网易云解灰已接入（端口 ' + p + '，来自渲染层）');
      }
      await reg.saveConfig();
    }
    return reg.status();
  });

  // 兼容旧 RPC 名字
  api.rpc.handle('status', whenReady(async function () {
    return reg.status();
  }));

  /* 诊断：解灰端口是否就位、能否真解析出一首歌。会主动探端口。 */
  api.rpc.handle('unblock.status', async function (probeId) {
    const id = String(probeId || '186016');
    const out = { port: neteaseUnblockPort, id: id, steps: [] };
    if (!neteaseUnblockPort) {
      const found = await discoverUnblockPort(reg.http, true);
      out.discovered = found;
      out.port = neteaseUnblockPort;
      if (!found) {
        out.error = '扫描本机临时端口段未找到解灰后端（' +
          EPHEMERAL_RANGES.map(function (r) { return r[0] + '-' + r[1]; }).join(' / ') + '）';
        return out;
      }
    }
    const url = unblockUrl(id, 'lossless');
    out.url = url;
    let raw = null;
    try {
      const r = await reg.http.httpGet(url, { timeout: 12000 });
      out.steps.push({ step: 'httpGet', status: r.status, bytes: r.buf.length });
      raw = r.buf.toString('utf8');
      out.rawHead = raw.slice(0, 300);
    } catch (err) {
      out.steps.push({ step: 'httpGet', err: String((err && err.message) || err) });
      return out;
    }
    let j = null;
    try {
      j = JSON.parse(raw);
    } catch (err) {
      out.steps.push({ step: 'parse', err: String((err && err.message) || err) });
      return out;
    }
    const d = (j && j.data && j.data[0]) || null;
    out.steps.push({ step: 'shape', code: j && j.code, hasData: !!d, hasUrl: !!(d && d.url) });
    if (d && d.url) {
      try {
        const p = await reg.http.probe(d.url, { Referer: 'https://music.163.com/' });
        out.probe = p;
      } catch (err) {
        out.steps.push({ step: 'probe', err: String((err && err.message) || err) });
      }
    }
    return out;
  });

  // 异步启动，不阻塞宿主
  ready
    .then(function () {
      const st = reg.status();
      const bad = st.units.filter(function (u) { return u.ok === false; });
      api.log.info(
        '音源就绪：启用 ' + st.enabled + ' / 共 ' + st.total +
          '（音质 ' + st.quality + '，跨平台回退 ' + (st.fallback ? '开' : '关') + '）'
      );
      if (bad.length) {
        api.log.warn(
          '部分音源加载失败',
          bad.map(function (u) { return u.name + ': ' + u.error; }).join(' | ')
        );
      }
      /* 启动即探解灰端口：否则第一首歌会在「还没探到」的窗口里退回翻唱。 */
      discoverUnblockPort(reg.http, true)
        .then(function (port) {
          if (port) api.log.info('网易云解灰已接入（端口 ' + port + '）：版权原唱可解析');
          else api.log.info('未发现网易云解灰后端，版权原唱将退回常规链');
        })
        .catch(function () {
          /* 探测失败不影响其它音源 */
        });
    })
    .catch(function (err) {
      api.log.error('音源初始化失败', String(err));
    });

  return function () {
    reg.songCache.clear();
    reg.lxUnits = [];
  };
};
