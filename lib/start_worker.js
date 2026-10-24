import {createEngine} from "./ffi_engine.js"
import {prepare} from "./prepare_util.js"
import {loadManifest, makeLoader, normModuleName} from "./module_loader.js"

// start_worker(include_dirs, client_lua, worker_lua)
//   include_dirs: legacy arg, kept for signature compatibility — module
//                 resolution now goes through <lua_root>/modules.json
//   client_lua:   module run in the main-thread engine
//   worker_lua:   module run in the spawned Worker (util_worker.js)
// legacy 2-arg form start_worker(client_lua, worker_lua) is accepted.
export async function start_worker(add_include_dirs, client_lua, worker_lua) {
    if (worker_lua === undefined && typeof add_include_dirs === "string") {
        [add_include_dirs, client_lua, worker_lua] =
            [[], add_include_dirs, client_lua]
    }
    let lua_root = new URL(import.meta.url).pathname;
    lua_root = lua_root.substring(0, lua_root.lastIndexOf("/"));
    lua_root = lua_root.substring(0, lua_root.lastIndexOf("/"));
    let worker = new Worker(lua_root + "/lib/util_worker.js", {type:"module"})

    const eng = await createEngine()
    const lua = eng.lua
    const manifest = await loadManifest(lua_root, eng.fetchText)
    const ensure = makeLoader(eng.registerSources, eng.fetchText,
                              lua_root, manifest)

    await ensure(client_lua)           // dep closure incl. lib.util
    await prepare(eng)                 // js bridges
    await lua.run(`result = require("${normModuleName(client_lua)}")`)
    let dotask = lua.run(`return result`)[0]

    function post_message(m) {
        worker.postMessage(m)
    }

    eng.setGlobal("__emh_post_message", function () {
        return post_message(this === globalThis ? undefined : this)
    }, false)
    await lua.run(`require("lib.util").set_js_post_message(__emh_post_message)
                   __emh_post_message = nil`)
    let done = false

    worker.onmessage = function(e) {
        if (e.data === "lkq23rlkj*(YkPOILHsdf23PsifjbUI234rg_-3ksdjl") {
            done = true
        } else {
            dotask(e.data)
        }
    }

    while (!done) {
        await new Promise(r => setTimeout(r, 100));
        worker.postMessage(
            JSON.stringify({command: "require", data: worker_lua,
                            include_dirs: add_include_dirs})
        )
    }
}
