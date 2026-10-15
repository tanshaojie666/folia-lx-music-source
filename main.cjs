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
  function makeAgg(id, name, short, searchServers, urlServer) {
    return {
      id: id,
      name: name,
      short: short,
      lossless: true,

      async search(q, limit, offset) {
        const seen = {};
        const out = [];

        for (const server of searchServers) {
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
            const key = it.name + '\u0000' + it.artist;
            if (seen[key]) continue;
            seen[key] = 1;
            out.push({
              id: sid,
              title: it.name || '',
              artist: it.artist || '',
              album: '',
              cover: it.pic || '',
              durationMs: 0,
              _urlServer: server === 'kugou' ? 'kugou' : urlServer,
            });
          }
          if (out.length >= limit) break;
        }

        return out.slice(offset, offset + limit);
      },

      async url(song, quality) {
        const id = song.id;
        const server = song._urlServer || urlServer;
        const chain = [];

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

        return resolveChain(http, chain, quality, { Referer: 'https://music.163.com/' });
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

  const wy = makeAgg('wy', '网易云（聚合）', '网', ['netease'], 'netease');
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

  sourcesDir() {
    return path.join(__dirname, 'sources');
  }

  ensureDir() {
    try {
      fs.mkdirSync(this.sourcesDir(), { recursive: true });
    } catch {
      /* 已存在 */
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
      await reg.saveConfig();
    }
    return reg.status();
  });

  // 兼容旧 RPC 名字
  api.rpc.handle('status', whenReady(async function () {
    return reg.status();
  }));

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
    })
    .catch(function (err) {
      api.log.error('音源初始化失败', String(err));
    });

  return function () {
    reg.songCache.clear();
    reg.lxUnits = [];
  };
};
