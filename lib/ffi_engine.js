// Engine adapter over the lua-5.4.7-with-ffi runtime (lua-interop.js).
// Loading model identical to bn's server/src/service.mjs: sources are
// fetched JS-side (async) and registered in package.preload, so Lua
// require stays synchronous — no fetch() inside Lua.
//
// Runtime file layout: lua-interop.js + lua-5.4.7-with-ffi.{js,wasm}
// sit next to this module in consumers (teaching: lua/lib) or in
// ../dist relative to js/ inside the lua-base repo itself.

let fs = null;
if (typeof process !== 'undefined' && process.versions?.node) {
    try { fs = await import('node:fs'); } catch (_) { }
}

function toURL(s) {
    s = s.replace(/\/+$/, '');          // 'a/b//' would eat '../' hops
    return s.includes('://') ? new URL(s + '/') : new URL('file://' + s + '/');
}

async function importInterop(here) {
    const hereURL = toURL(here);
    for (const base of [hereURL.href, new URL('../dist/', hereURL).href]) {
        try {
            const m = await import(new URL('lua-interop.js', base).href);
            return { interop: m, base };
        } catch (_) { }
    }
    throw new Error('ffi_engine: lua-interop.js not found near ' + here);
}

// opts.baseUrl: URL/dir where the runtime files live (default: next to
// this module, with ../dist as fallback for the lua-base checkout)
export async function createEngine(opts = {}) {
    const here = opts.baseUrl || new URL('./', import.meta.url).href;
    const { interop, base } = await importInterop(here);

    const lua = await interop.newLua({
        luaJSPath:  new URL('lua-5.4.7-with-ffi.js', base).href,
        locateFile: () => new URL('lua-5.4.7-with-ffi.wasm', base).href,
        print:    opts.print    || (s => console.log('[lua]', s)),
        printErr: opts.printErr || (s => console.error('[lua]', s)),
    });
    // luaopen_js touches `window`; in workers/Node that is globalThis
    globalThis.window ??= globalThis;
    await lua.newState();
    // marker for library code: under Emscripten, dlopen can only load
    // wasm side modules that are already present in MEMFS
    lua.run('__wasm_env = true');

    // Fetch a Lua source; file:// goes through node:fs.  Over HTTP the
    // compressed siblings <url>.br then <url>.gz are probed (whichever
    // codec DecompressionStream supports — 'brotli' needs a newer
    // engine, 'gzip' is universal) and inflated — static hosts
    // (GitHub Pages) compress only whitelisted MIME types and
    // text/x-lua is not one, so deployments ship precompressed sources
    // next to the plain files.  Absent or undecodable siblings fall
    // back to the plain fetch.  A ?v=<deploy-hash> URL is
    // content-stamped and can live in the browser cache forever;
    // unstamped URLs keep no-store so edits are picked up immediately.
    const cacheMode = (url) => /[?&]v=[0-9a-f]+/.test(url)
        ? 'force-cache' : 'no-store';
    async function fetchText(url) {
        if (fs && String(url).startsWith('file:')) {
            return fs.readFileSync(new URL(url), 'utf8');
        }
        const cm = cacheMode(String(url));
        if (typeof DecompressionStream !== 'undefined') {
            // string surgery, not new URL(): callers may pass relative
            // paths which URL() would reject without a base
            for (const [fmt, ext] of [['brotli', '.br'], ['gzip', '.gz']]) {
                let ds;
                try { ds = new DecompressionStream(fmt); }
                catch (_) { continue; }  // codec unsupported
                const cu = String(url).replace(/([?#].*)?$/, ext + '$1');
                const cr = await fetch(cu, { cache: cm });
                if (cr.ok) {
                    try {
                        const body = cr.body.pipeThrough(ds);
                        return await new Response(body).text();
                    } catch (_) { /* fall through to the next codec */ }
                }
            }
        }
        const r = await fetch(url, { cache: cm });
        if (!r.ok) throw new Error('cannot load ' + url + ': HTTP ' + r.status);
        return r.text();
    }

    async function fetchBytes(url) {
        if (fs && String(url).startsWith('file:')) {
            return fs.readFileSync(new URL(url));
        }
        const r = await fetch(url, { cache: cacheMode(String(url)) });
        if (!r.ok) throw new Error('cannot load ' + url + ': HTTP ' + r.status);
        return new Uint8Array(await r.arrayBuffer());
    }

    const M = lua.lib, L = lua.L;

    // opts.dynLibs: { name: url } — wasm side modules (emcc
    // -sSIDE_MODULE=1) fetched now and staged in MEMFS at
    // __wasm_dynlib_dir/<name>.wasm, so a later synchronous
    // package.loadlib(<dir>/<name>.wasm, openfn) works.
    const dynDir = '/dynlib';
    if (opts.dynLibs) {
        M.FS.mkdirTree(dynDir);
        for (const [name, url] of Object.entries(opts.dynLibs)) {
            M.FS.writeFile(dynDir + '/' + name + '.wasm',
                           await fetchBytes(url));
        }
        lua.run('__wasm_dynlib_dir = ...', dynDir);
    }

    // lua-interop holds JS objects only via WeakRef — once the JS side
    // drops the last reference the Lua proxy derefs to undefined and
    // calls explode with "undefined.apply".  Pin every injected value
    // for the engine's lifetime; injected globals are meant to persist.
    const pinned = [];

    // push a JS value into a Lua global.  isArrow=true picks the
    // positional calling convention — without it the first Lua argument
    // lands on JS `this` (lua-interop's colon-call convention)
    function setGlobal(name, value, isArrow = true) {
        pinned.push(value);
        M._lua_pushglobaltable(L);
        lua.push(L, value, isArrow);
        M._lua_setfield(L, -2, M.stringToNewUTF8(name));
        M._lua_pop(L, 1);
    }

    // register {moduleName: source} into package.preload — deferred
    // until require'd (bn's service.mjs block, verbatim semantics)
    function registerSources(sources) {
        lua.run(`
            local sources = ...
            if type(sources) == "table" then
                for name, src in pairs(sources) do
                    package.preload[name] = function()
                        local chunk, err = load(src, name)
                        if not chunk then error(err) end
                        return chunk()
                    end
                end
            end
        `, sources);
    }

    return { lua, M, L, setGlobal, fetchText, registerSources };
}
