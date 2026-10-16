// 洛雪音源 → Folia (Folium) · client 入口（渲染进程）
//
// 职责：
//   1. 给「每个已启用音源」注册一个独立的 omni provider —— 这就是"可选音源"：
//      用户在设置里关掉哪个，哪个就从 Folia 的搜索来源列表里消失。
//   2. 注册设置区（音质 / 跨平台回退 / 启用清单）。
//   3. 注册命令（添加音源 / 移除音源 / 启用 / 停用 / 状态 / 重载）。
//
// 所有实际工作都在 main 进程，这里只做注册与转发。

const PROVIDER_PREFIX = 'lxs-';

function slug(s) {
  return String(s || '')
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, '-')
    .replace(/^-+|-+$/g, '')
    .slice(0, 24);
}

function shortHash(s) {
  let h = 2166136261;
  const str = String(s);
  for (let i = 0; i < str.length; i++) {
    h ^= str.charCodeAt(i);
    h = Math.imul(h, 16777619);
  }
  return (h >>> 0).toString(36);
}

// provider id 必须是稳定安全串；人类可读的部分交给 displayName。
function providerId(unit) {
  const s = slug(unit.slug || unit.name || unit.id) || 'src';
  return `${PROVIDER_PREFIX}${s}-${shortHash(unit.id)}`;
}

export default function activate(folium) {
  const log = folium.log;
  const minor = folium.host?.folium?.minor ?? 0;

  const omni = folium.experimental?.['omni.providers'];
  if (!omni || typeof omni.register !== 'function') {
    log.error('omni.providers 不可用：请确认 mod.json 里声明了 experimental: ["omni.providers"]');
    return;
  }

  const rpc = (name, ...args) => folium.rpc.call(name, ...args);

  /* ---------------- provider 挂载 ---------------- */

  let handles = [];
  let mountedKey = '';

  function unmountAll() {
    for (const h of handles) {
      try {
        h?.unregister?.();
      } catch {
        /* 宿主停用时自己也会撤下 */
      }
    }
    handles = [];
  }

  function makeProvider(unit) {
    return {
      id: providerId(unit),
      displayName: unit.name,
      shortName: unit.short || unit.name.slice(0, 2),

      async search(query, page) {
        const limit = Number(page?.limit) || 30;
        const offset = Number(page?.offset) || 0;
        const res = await rpc('source.search', unit.id, String(query ?? ''), limit, offset);
        if (!res || !Array.isArray(res.items)) return { items: [], hasMore: false };
        return {
          items: res.items,
          hasMore: !!res.hasMore,
          ...(Number.isFinite(res.total) ? { total: res.total } : {}),
        };
      },

      async getSong(id) {
        try {
          return await rpc('source.song', unit.id, String(id));
        } catch (err) {
          log.warn(`[${unit.name}] getSong 失败`, String(err));
          return null;
        }
      },

      async getAudioUrl(song, quality) {
        try {
          const res = await rpc('source.url', unit.id, String(song.id), String(quality || 'lossless'));
          if (!res || typeof res.url !== 'string') return null;
          const out = { url: res.url };
          if (Number.isFinite(res.expiresAt)) out.expiresAt = res.expiresAt;
          if (res.quality) out.quality = res.quality;
          return out;
        } catch (err) {
          log.warn(`[${unit.name}] 取链失败：${song?.title ?? ''}`, String(err));
          return null;
        }
      },

      async getLyrics(song) {
        try {
          const res = await rpc('source.lyric', unit.id, String(song.id));
          const text = typeof res === 'string' ? res : res?.text;
          if (!text || !String(text).trim()) return null;
          if (minor >= 4) return { main: { format: 'lrc', text: String(text) } };
          return { lrc: String(text) };
        } catch {
          return null;
        }
      },
    };
  }

  async function mountAll(force) {
    let list;
    try {
      list = await rpc('sources.list');
    } catch (err) {
      log.error('读取音源清单失败', String(err));
      return;
    }

    const units = (list?.units || []).filter((u) => u.enabled && u.ok !== false);
    const key = units.map((u) => u.id).sort().join('|');
    if (!force && key === mountedKey) return;

    unmountAll();

    const failed = [];
    for (const unit of units) {
      try {
        handles.push(omni.register(makeProvider(unit)));
      } catch (err) {
        failed.push(`${unit.name}: ${err?.message ?? err}`);
      }
    }

    mountedKey = key;
    const okNames = units.map((u) => u.name);
    if (okNames.length) log.info(`已挂载 ${okNames.length} 个音源：${okNames.join('、')}`);
    if (failed.length) log.warn('部分音源注册失败', failed.join(' | '));

    const disabled = (list?.units || []).filter((u) => !u.enabled).map((u) => u.name);
    if (disabled.length) log.info(`已停用：${disabled.join('、')}（用「音源状态」查看，用「启用音源」开启）`);
  }

  /* ---------------- 设置区 ---------------- */

  let settingsAccess = null;

  function registerSettings() {
    const sections = folium.registries?.settingsSections;
    if (!sections || typeof sections.register !== 'function') {
      log.warn('registries.settingsSections 不可用，跳过设置区注册（命令仍可用）');
      return;
    }
    try {
      settingsAccess = sections.register({
        id: 'sources',
        label: { 'zh-CN': '音源设置', en: 'Music sources' },
        description: {
          'zh-CN': '音质、跨平台回退、启用清单。添加/移除音源请用「命令」里的添加音源 / 移除音源。',
          en: 'Quality, cross-platform fallback and the enabled list.',
        },
        settings: [
          {
            key: 'quality',
            type: 'select',
            label: { 'zh-CN': '音质', en: 'Quality' },
            description: {
              'zh-CN': '无损档优先取 FLAC，取不到再逐级降级。',
              en: 'Lossless tries FLAC first, then degrades step by step.',
            },
            defaultValue: 'lossless',
            options: [
              { value: 'hires', label: { 'zh-CN': '无损 24bit', en: 'Hi-Res' } },
              { value: 'lossless', label: { 'zh-CN': '无损', en: 'Lossless' } },
              { value: 'high', label: { 'zh-CN': '较高 320k', en: 'High 320k' } },
              { value: 'standard', label: { 'zh-CN': '标准 128k', en: 'Standard 128k' } },
            ],
          },
          {
            key: 'fallback',
            type: 'boolean',
            label: { 'zh-CN': '跨平台回退', en: 'Cross-platform fallback' },
            description: {
              'zh-CN': '本平台取不到无损时，用「歌名 + 歌手」去网易云再取一次。',
              en: 'When this platform has no lossless URL, retry on NetEase by title + artist.',
            },
            defaultValue: true,
          },
          {
            key: 'enabledSources',
            type: 'text',
            label: { 'zh-CN': '启用清单', en: 'Enabled list' },
            description: {
              'zh-CN': '逗号分隔的音源 id。留空=全部启用；填了则只启用列出的那些。',
              en: 'Comma-separated source ids. Empty = enable all.',
            },
            defaultValue: '',
          },
        ],
      });
    } catch (err) {
      log.warn('设置区注册失败（字段类型可能不被支持），命令仍然可用', String(err?.message ?? err));
      settingsAccess = null;
    }
  }

  // 把设置区里的值同步给 main（宿主没暴露变更订阅，用低频轮询）
  let lastPushed = '';
  let lastPort = 0;

  /* 解灰端口：Folia 主进程里的网易云后端起在动态端口上，只有渲染层
   * （此处）能通过 window.electron.getNeteasePort() 问到。主进程拿到它之后，
   * 就能用 /song/url/v1?...&unblock=true 解析版权原唱（实测「晴天」269.75s 完整版）。
   * 端口在 Folia 重启后会变，所以每次轮询都比对一次。 */
  async function readUnblockPort() {
    try {
      const p = await window.electron?.getNeteasePort?.();
      const n = Number(p);
      return Number.isInteger(n) && n > 0 && n < 65536 ? n : 0;
    } catch {
      return 0;
    }
  }

  /* 诊断：确认本模块能看到的全局对象（模组跑在隔离上下文里，
   * window.electron 未必可见，这决定端口从哪来）。 */
  try {
    log.info(
      '上下文自检：electron=' + typeof window.electron +
        ' folium=' + typeof window.folium +
        ' getPort=' + typeof window.electron?.getNeteasePort +
        ' hostKeys=' + Object.keys(folium.host || {}).join(',')
    );
  } catch (e) {
    log.warn('上下文自检失败', String(e?.message ?? e));
  }

  async function pushSettings() {
    /* 端口与设置区是**独立**的两件事：设置区注册失败时（宿主版本差异、
     * sections 不可用等）也必须把解灰端口送进主进程，否则版权原唱会静默
     * 退回翻唱。所以先无条件上报端口，再处理设置值。 */
    const port = await readUnblockPort();

    let values = null;
    try {
      values = settingsAccess?.get ? settingsAccess.get() : null;
    } catch {
      values = null;
    }

    const payload = {
      quality: values?.quality,
      fallback: values?.fallback,
      enabledSources: values?.enabledSources,
      unblockPort: port,
    };
    const key = JSON.stringify(payload);
    if (key === lastPushed) return;
    lastPushed = key;

    try {
      await rpc('config.sync', payload);
      if (port && port !== lastPort) {
        lastPort = port;
        log.info(`网易云解灰端口 ${port} 已交给音源后端`);
      }
    } catch (err) {
      log.warn('同步音源设置失败', String(err));
      lastPushed = ''; // 失败就允许下一轮重试
      return;
    }

    if (values) {
      try {
        await mountAll(true);
      } catch (err) {
        log.warn('挂载音源失败', String(err));
      }
    }
  }

  /* ---------------- 命令 ---------------- */

  function registerCommands() {
    const commands = folium.registries?.commands;
    if (!commands || typeof commands.register !== 'function') {
      log.warn('registries.commands 不可用，跳过命令注册');
      return;
    }

    const defs = [
      {
        id: 'source-status',
        label: { 'zh-CN': '音源状态', en: 'Source status' },
        description: { 'zh-CN': '列出全部音源及其启用状态', en: 'List every source and its state' },
        run: async () => {
          const list = await rpc('sources.list');
          const units = list?.units || [];
          const on = units.filter((u) => u.enabled && u.ok !== false);
          const off = units.filter((u) => !u.enabled);
          const bad = units.filter((u) => u.ok === false);
          const lines = [
            `启用 ${on.length} / 共 ${units.length}`,
            '',
            ...on.map(
              (u) =>
                `[开] ${u.name}  (${u.id})  ${u.kind === 'direct' ? '内置' : '脚本'}  ${u.lossless ? '支持无损' : '普通音质'}`
            ),
            ...off.map((u) => `[关] ${u.name}  (${u.id})`),
            ...bad.map((u) => `[错] ${u.name}  (${u.id})  ${u.error || '加载失败'}`),
          ];
          return { message: lines.join('\n'), warnings: bad.map((u) => `${u.name}: ${u.error}`) };
        },
      },
      {
        id: 'source-enable',
        label: { 'zh-CN': '启用音源', en: 'Enable source' },
        description: { 'zh-CN': '按 id 启用一个音源', en: 'Enable one source by id' },
        params: [{ key: 'id', type: 'text', label: { 'zh-CN': '音源 id', en: 'Source id' } }],
        run: async ({ values }) => {
          const id = String(values?.id ?? '').trim();
          if (!id) return { message: '需要提供音源 id' };
          const res = await rpc('sources.toggle', id, true);
          await mountAll(true);
          return { message: res?.ok ? `已启用：${res.name ?? id}` : `启用失败：${res?.error ?? '未知音源'}` };
        },
      },
      {
        id: 'source-disable',
        label: { 'zh-CN': '停用音源', en: 'Disable source' },
        description: { 'zh-CN': '按 id 停用一个音源', en: 'Disable one source by id' },
        params: [{ key: 'id', type: 'text', label: { 'zh-CN': '音源 id', en: 'Source id' } }],
        run: async ({ values }) => {
          const id = String(values?.id ?? '').trim();
          if (!id) return { message: '需要提供音源 id' };
          const res = await rpc('sources.toggle', id, false);
          await mountAll(true);
          return { message: res?.ok ? `已停用：${res.name ?? id}` : `停用失败：${res?.error ?? '未知音源'}` };
        },
      },
      {
        id: 'source-add',
        label: { 'zh-CN': '添加音源', en: 'Add source' },
        description: {
          'zh-CN': '从本地 .js 路径或 http(s) 链接添加一个洛雪音源脚本',
          en: 'Add a LX source script from a local .js path or an http(s) URL',
        },
        params: [
          {
            key: 'target',
            type: 'text',
            label: { 'zh-CN': '路径或链接', en: 'Path or URL' },
            description: {
              'zh-CN': '例如 C:\\Users\\me\\Downloads\\源.js 或 https://example.com/source.js',
              en: 'e.g. C:\\path\\source.js or https://example.com/source.js',
            },
          },
          {
            key: 'name',
            type: 'text',
            label: { 'zh-CN': '音源名称（可选）', en: 'Name (optional)' },
          },
        ],
        run: async ({ values }) => {
          const target = String(values?.target ?? '').trim();
          if (!target) return { message: '需要提供路径或链接' };
          const name = String(values?.name ?? '').trim();
          const res = await rpc('sources.add', target, name || null);
          if (!res?.ok) return { message: `添加失败：${res?.error ?? '未知错误'}` };
          await mountAll(true);
          const w = res.warnings || [];
          return {
            message: `已添加并启用：${res.name}\n文件：${res.file}${w.length ? `\n注意：\n${w.join('\n')}` : ''}`,
            warnings: w,
          };
        },
      },
      {
        id: 'source-remove',
        label: { 'zh-CN': '移除音源', en: 'Remove source' },
        description: {
          'zh-CN': '删除一个已添加的音源（含脚本文件）',
          en: 'Delete an added source and its script file',
        },
        params: [{ key: 'id', type: 'text', label: { 'zh-CN': '音源 id', en: 'Source id' } }],
        run: async ({ values }) => {
          const id = String(values?.id ?? '').trim();
          if (!id) return { message: '需要提供音源 id' };
          const res = await rpc('sources.remove', id);
          if (!res?.ok) return { message: `移除失败：${res?.error ?? '未知错误'}` };
          await mountAll(true);
          return { message: `已移除：${res.name ?? id}` };
        },
      },
      {
        id: 'source-reload',
        label: { 'zh-CN': '重载音源', en: 'Reload sources' },
        description: {
          'zh-CN': '重新扫描 sources/ 目录并重新挂载全部音源',
          en: 'Rescan sources/ and remount everything',
        },
        run: async () => {
          const res = await rpc('sources.reload');
          await mountAll(true);
          const units = res?.units || [];
          const on = units.filter((u) => u.enabled && u.ok !== false).length;
          const bad = units.filter((u) => u.ok === false);
          return {
            message:
              `重载完成：启用 ${on} / 共 ${units.length}` +
              (bad.length ? `\n失败：${bad.map((u) => `${u.name}(${u.error})`).join(', ')}` : ''),
            warnings: bad.map((u) => `${u.name}: ${u.error}`),
          };
        },
      },
    ];

    for (const def of defs) {
      try {
        commands.register(def);
      } catch (err) {
        log.warn(`命令注册失败：${def.id}`, String(err?.message ?? err));
      }
    }
  }

  /* ---------------- 启动 ---------------- */

  registerSettings();
  registerCommands();

  mountAll(true).catch((err) => log.error('挂载音源失败', String(err)));

  // 立刻上报一次：解灰端口不能等 4 秒轮询，否则首次播放会退回翻唱。
  pushSettings().catch(() => {});

  const timer = setInterval(() => {
    pushSettings().catch(() => {});
  }, 4000);

  return () => {
    clearInterval(timer);
    unmountAll();
  };
}
