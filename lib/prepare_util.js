// Inject the JS-side bridges lib.util expects (js_get/js_set,
// js_post_message, Intl.Segmenter) into an ffi_engine engine.
//
// lua-interop's calling convention: the first Lua argument arrives as
// JS `this`, remaining args positionally — `call0` folds this back.
// (wasmoon exposed :await() on promises; this runtime does not — module
// loading is handled JS-side via module_loader instead.)

function call0(f) {
    return function () { return f.call(null, this, ...arguments); };
}

export async function prepare(eng) {
    const { lua } = eng;

    eng.setGlobal('__emh_eval',       call0(s => eval(s)), false);
    eng.setGlobal('__emh_array_from', call0(it => Array.from(it)), false);
    if (typeof Intl !== 'undefined' && Intl.Segmenter) {
        const seg = new Intl.Segmenter('en', { granularity: 'grapheme' });
        // obj.prop fetched through lua-interop's __index arrives
        // owner-bound with positional args; the `this` fallback keeps
        // the injection working under an unpatched interop (arg-as-this).
        eng.setGlobal('__emh_segmenter',
            { segment: function (s) {
                return seg.segment(s !== undefined ? s : this);
            } }, false);
    }
    if (typeof postMessage !== 'undefined') {
        eng.setGlobal('__emh_post_message',
            function () { return postMessage(this); }, false);
    }

    await lua.run(`
        local util = require "lib.util"
        util.js_set("eval", __emh_eval)
        util.js_set("Array.from", __emh_array_from)
        if __emh_segmenter then
            util.set_js_intl_segmenter(__emh_segmenter)
        end
        if __emh_post_message then
            util.set_js_post_message(__emh_post_message)
        end
        __emh_eval, __emh_array_from, __emh_segmenter, __emh_post_message =
            nil, nil, nil, nil
    `);
}
