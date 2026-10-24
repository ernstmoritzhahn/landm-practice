import {createEngine} from "./ffi_engine.js"
import {prepare} from "./prepare_util.js"
import {loadManifest, makeLoader, normModuleName} from "./module_loader.js"

let server_function = null
let ensure = null

const eng = await createEngine()
const lua = eng.lua

// .../lua/lib/util_worker.js -> lua root (strip "lib/util_worker.js")
let path = self.location.pathname;
path = path.substring(0, path.length - 19);

// serialise messages: a repeated "require" burst must not init twice
let chain = Promise.resolve()

async function handle(e) {
    let message = JSON.parse(e.data)
    if (message.command === "require") {
        if (server_function == null) {
            if (ensure == null) {
                const manifest = await loadManifest(path, eng.fetchText)
                ensure = makeLoader(eng.registerSources, eng.fetchText,
                                    path, manifest)
            }
            await ensure(message.data)
            await prepare(eng)
            server_function = lua.run(
                `return require("${normModuleName(message.data)}")`)[0]
        }
        postMessage("lkq23rlkj*(YkPOILHsdf23PsifjbUI234rg_-3ksdjl")
    } else if (server_function != null) {
        server_function(e.data)
    }
}

onmessage = function(e) {
    chain = chain.then(() => handle(e)).catch(
        err => console.error("[util_worker]", err))
}
