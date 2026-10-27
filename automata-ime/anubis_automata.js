/* <automata-app> — Anubis-plugin wrapper around the automata-ime
 * wasm build (make web).  Classic-script file: load it as pluginjs
 * and put <automata-app></automata-app> in pluginhtml.
 *
 * Anubis lifecycle:
 *   initializeApplication(arg) — arg is the text between @@ markers
 *       in the .exam (JSON: {mode:"aut"|"re", alphabet:"a,b",
 *       aut_type:"nfa"|"nfa-eps"|"dfa"|"dfa-part", checks:{...},
 *       initial:{...model...}})
 *   loadData(arg)     — restores the string retrieveData returned
 *   retrieveData()    — answer JSON; "" means unanswered
 *   setReadOnly(bool) — review mode (all mutation paths frozen)
 *   sendDataToExternal event — dispatched ~250ms after each edit
 *
 * The element boots one Emscripten module per instance: shadow-DOM
 * canvas, in-page VFS writes from ui-data.js, then _main.  The
 * server/checks link is the in-process loopback (nkl_lua_service —
 * ui.lua's ui_service global), so no worker or socket is needed.
 */
(function () {
    "use strict";
    var BASE = "";
    /* deploy token — stage_proof_site.py stamps b9452fb876e0 with a
     * hash over the whole bundle; every asset URL carries it so a
     * redeploy can never serve a stale mix.  Unstaged (literal
     * placeholder) URLs stay clean so local serving keeps working. */
    var AUT_V = "b9452fb876e0";
    function vurl(u) {
        return (AUT_V.charAt(0) === "_") ? u : u + "?v=" + AUT_V;
    }
    try {
        /* document.currentScript is null when the host injects us as a
         * module or via eval (Anubis does exactly that), so also look up
         * our own <script src> element — it is already in the DOM by the
         * time this body runs. */
        var sc = (document.currentScript && document.currentScript.src)
            ? document.currentScript.src
            : (function () {
                var s = document.querySelector(
                    "script[src*='anubis_automata.js']");
                return s ? s.src : null;
            })();
        if (!sc) throw new Error("no script url");
        BASE = new URL(".", sc).href;
    } catch (e) {
        /* last resort: the exam assets live under the URL's directory —
         * but a trailing segment without a dot is an id (…/506), not a
         * file, so keep it with a slash instead of stripping it. */
        var p = location.pathname;
        var last = p.slice(p.lastIndexOf("/") + 1);
        if (last && last.indexOf(".") < 0 && p.charAt(p.length - 1) !== "/")
            p += "/";
        else
            p = p.replace(/[^\/]*$/, "");
        BASE = location.origin + p;
    }

    /* ---------- shared, loaded once for all element instances -------- */
    // boot progress lands on a data attribute so failures are
    // inspectable without console access (Anubis pages offer none)
    function stage(el, s) {
        if (el) el.setAttribute("data-stage", s);
    }

    function loadScript(src) {
        return new Promise(function (res, rej) {
            var s = document.createElement("script");
            s.src = src;
            s.onload = res;
            s.onerror = function () { rej(new Error(src + " load failed")); };
            document.head.appendChild(s);
        });
    }

    function b64buf(s) {
        var b = atob(s), u = new Uint8Array(b.length);
        for (var i = 0; i < b.length; i++) u[i] = b.charCodeAt(i);
        return u;
    }

    // plugin-data.js stores each asset base64'd, gzip-compressed when
    // that wins (AUT_GZ): DecompressionStream inflates in-browser.
    async function blobBytes(key) {
        var u = b64buf(window.AUT_BLOB[key]);
        if (window.AUT_GZ && window.AUT_GZ[key]) {
            if (typeof DecompressionStream === "undefined")
                throw new Error("no DecompressionStream");
            var ds = new DecompressionStream("gzip");
            var rs = new Response(
                new Blob([u]).stream().pipeThrough(ds));
            return await rs.arrayBuffer();
        }
        return u.buffer;
    }

    var _assetsP = null;
    function assets(el) {
        if (_assetsP) return _assetsP;
        _assetsP = (async function () {
            var res = {};
            // ui-data.js + plugin-data.js are classic scripts setting
            // globals.  plugin-data.js carries every non-JS byte as
            // base64 — the only path past asset hosts that whitelist
            // extensions (Anubis serves .js/.css only, 403 otherwise).
            await loadScript(vurl(BASE + "ui-data.js"));
            stage(el, "uidata");
            res.uiData = window.UI_DATA;
            try { await loadScript(vurl(BASE + "plugin-data.js")); }
            catch (e) { /* standalone/mock: no bundle, plain fetches */ }
            var blob = window.AUT_BLOB || null;
            res.blob = blob;
            stage(el, blob ? "blob" : "fetch");
            if (blob && blob["unified.wasm"]) {
                try { res.wasm = await blobBytes("unified.wasm"); }
                catch (e) { res.wasm = null; }
            }
            if (!res.wasm) {
                var r = await fetch(vurl(BASE + "unified.wasm"));
                if (!r.ok) throw new Error("unified.wasm: HTTP " + r.status);
                res.wasm = await r.arrayBuffer();
            }
            stage(el, "wasm");
            res.factory = (await import(vurl(BASE + "unified.js"))).default;
            stage(el, "factory");
            return res;
        })();
        return _assetsP;
    }

    /* ---------- keyboard: semantic key resolution (as in ime.js) ----- */
    var nklPlatform = (function () {
        var p = navigator.platform || "";
        if (/Mac|iPhone|iPad|iPod/i.test(p)) return "mac";
        if (/Win/i.test(p)) return "win";
        return "linux";
    })();

    function resolveKey(e) {
        var isMac = nklPlatform === "mac";
        var isWin = nklPlatform === "win";
        var ctrl = e.ctrlKey, alt = e.altKey, meta = e.metaKey;
        if (e.key === "Shift") return ["Shift", false];
        if (e.key.length === 1 && (ctrl || alt || meta)) {
            var k = e.key.toLowerCase();
            if (isMac) {
                if (meta) { if (k === "a") return ["SelectAll", true]; }
                else if (ctrl) {
                    if (k === "a") return ["LineStart", true];
                    if (k === "e") return ["LineEnd", true];
                    if (k === "b") return ["ArrowLeft", true];
                    if (k === "f") return ["ArrowRight", true];
                    if (k === "p") return ["ArrowUp", true];
                    if (k === "n") return ["ArrowDown", true];
                    if (k === "d") return ["Delete", true];
                    if (k === "h") return ["Backspace", true];
                    if (k === "k") return ["DeleteLineEnd", true];
                    if (k === "u") return ["DeleteLineBack", true];
                    if (k === "w") return ["DeleteWordBack", true];
                }
            } else {
                if (ctrl && k === "a") return ["SelectAll", true];
                if (!isWin && alt) {
                    if (k === "b") return ["WordLeft", true];
                    if (k === "f") return ["WordRight", true];
                    if (k === "d") return ["DeleteWordForward", true];
                    if (k === "h") return ["DeleteWordBack", true];
                }
            }
            return null;
        }
        switch (e.key) {
            case "ArrowLeft":
                if (isMac && meta) return ["LineStart", true];
                if (!isMac && ctrl) return ["WordLeft", true];
                if (isMac && alt) return ["WordLeft", true];
                if (!isWin && !isMac && alt) return ["WordLeft", true];
                return ["ArrowLeft", true];
            case "ArrowRight":
                if (isMac && meta) return ["LineEnd", true];
                if (!isMac && ctrl) return ["WordRight", true];
                if (isMac && alt) return ["WordRight", true];
                if (!isWin && !isMac && alt) return ["WordRight", true];
                return ["ArrowRight", true];
            case "ArrowUp":
                if (isMac && meta) return ["DocStart", true];
                if (isMac && alt) return ["DocStart", true];
                if (!isMac && ctrl) return ["DocStart", true];
                return ["ArrowUp", true];
            case "ArrowDown":
                if (isMac && meta) return ["DocEnd", true];
                if (isMac && alt) return ["DocEnd", true];
                if (!isMac && ctrl) return ["DocEnd", true];
                return ["DocEnd", true];
            case "Home":
                if (isMac && meta) return ["DocStart", true];
                if (!isMac && ctrl) return ["DocStart", true];
                return ["LineStart", true];
            case "End":
                if (isMac && meta) return ["DocEnd", true];
                if (!isMac && ctrl) return ["DocEnd", true];
                return ["LineEnd", true];
            case "PageUp": return ["DocStart", true];
            case "PageDown": return ["DocEnd", true];
            case "Backspace":
                if (isMac && meta) return ["DeleteLineBack", true];
                if (ctrl) return ["DeleteWordBack", true];
                if (!isWin && alt) return ["DeleteWordBack", true];
                return ["Backspace", true];
            case "Delete":
                if (isMac && meta) return ["DeleteLineEnd", true];
                if (ctrl) return ["DeleteWordForward", true];
                if (!isWin && alt) return ["DeleteWordForward", true];
                return ["Delete", true];
            case "Enter": return ["Enter", true];
            case "Tab": return ["Tab", true];
            case "Escape": return ["Escape", true];
        }
        return null;
    }

    /* ---------- the element ------------------------------------------ */
    /* Emscripten's event-target resolution is
     *   V(sel) -> document.querySelector(sel)
     * and SDL registers its canvas handlers with the literal selector
     * "#canvas".  A canvas inside a shadow root is invisible to
     * querySelector, so without help SDL binds nothing and mouse input
     * is dead (the click reaches the DOM node but never nuklear).
     * Patch querySelector ONCE for the exact "#canvas" selector and
     * resolve it through a per-call slot that each instance arms right
     * before the C side may resolve it (SDL init inside _main, and
     * every web_resize) and clears again right after.  While armed the
     * slot wins even over a real light-DOM #canvas — Anubis pages DO
     * contain one (the UTML editor), and a miss-only fallback would
     * bind SDL's mouse listeners to THAT element instead.  The arming
     * windows are synchronous, so no other caller can be affected. */
    if (!document.__autQueryPatched) {
        document.__autQueryPatched = true;
        var _origQS = document.querySelector.bind(document);
        document.querySelector = function (sel) {
            if (sel === "#canvas" && window.__autCanvasSlot)
                return window.__autCanvasSlot;
            return _origQS(sel);
        };
    }

    class AutomataApp extends HTMLElement {
        constructor() {
            super();
            this._pending = {};      // hooks called before boot finished
            this._lastDirty = -1;
            this._poll = null;
        }

        connectedCallback() {
            if (this._boot) return;
            var self = this;
            self.setAttribute("data-stage", "boot");
            this._boot = this._start().catch(function (e) {
                self.setAttribute("data-stage",
                    "err:" + String((e && (e.message || e)) || e).slice(0, 120));
                console.error("automata-app:", e);
            });
        }

        disconnectedCallback() {
            if (this._poll) { clearInterval(this._poll); this._poll = null; }
        }

        async _start() {
            var self = this;
            var root = this.attachShadow({ mode: "open" });
            root.innerHTML =
                "<style>" +
                /* the UI is designed for 800x600 — a shorter box makes
                 * the Lua side shrink geometry AND (at bake time) the
                 * font below the 18px the page text uses, so keep the
                 * element tall enough for full scale */
                ":host{display:block;min-height:600px;position:relative}" +
                "canvas{position:absolute;inset:0;width:100%;" +
                "height:100%;outline:none;touch-action:none}" +
                "#load{position:absolute;inset:0;display:flex;" +
                "align-items:center;justify-content:center;" +
                "font:14px arial,sans-serif;color:#777;background:#f8f8f8}" +
                "</style>" +
                "<canvas id=canvas></canvas>" +
                "<div id=load>Loading automaton editor&hellip;</div>";
            var canvas = root.getElementById("canvas");
            var load = root.getElementById("load");

            /* Emscripten resolves "#canvas" LIVE while translating
             * mouse events (css-size lookup scales clientX/Y to the SDL
             * window) — not only when binding listeners.  The exam page
             * carries its own light-DOM #canvas (the UTML editor), so
             * the slot must stay armed for as long as the pointer is
             * over THIS canvas, including drags outside the box.
             * pointerenter always precedes pointerdown, and the
             * pointerup listener re-evaluates on release outside. */
            canvas.addEventListener("pointerenter", function () {
                window.__autCanvasSlot = canvas;
            });
            canvas.addEventListener("pointerdown", function () {
                window.__autCanvasSlot = canvas;
            });
            canvas.addEventListener("pointerleave", function (e) {
                if (!(e.buttons & 7) && window.__autCanvasSlot === canvas)
                    window.__autCanvasSlot = null;
            });
            document.addEventListener("pointerup", function (e) {
                if (window.__autCanvasSlot !== canvas) return;
                var r = canvas.getBoundingClientRect();
                if (e.clientX < r.left || e.clientX >= r.right ||
                    e.clientY < r.top  || e.clientY >= r.bottom)
                    window.__autCanvasSlot = null;
            });

            var A = await assets(this);
            var Module = {
                canvas: canvas,
                noInitialRun: true,
                wasmBinary: A.wasm,
                instantiateWasm: function (imports, done) {
                    WebAssembly.instantiate(A.wasm, imports).then(
                        function (out) { done(out.instance, out.module); });
                    return {};
                },
                print: function (t) { console.log("automata:", t); },
                printErr: function (t) { console.warn("automata:", t); },
            };
            this._mod = await A.factory(Module);
            stage(this, "module");
            var FS = this._mod.FS;
            // plain-file fetch only — the .br/.gz siblings stay for the
            // standalone shell; four at a time like the demo boot so a
            // lightweight exam server is not hit with a burst
            for (var i = 0; i < A.uiData.length; i += 4) {
                var batch = A.uiData.slice(i, i + 4);
                await Promise.all(batch.map(function (f) {
                    var p;
                    if (A.blob && A.blob[f.url]) {
                        p = blobBytes(f.url).catch(function () {
                            return fetch(vurl(BASE + f.url))
                                .then(function (r) {
                                if (!r.ok)
                                    throw new Error(f.url + ": HTTP "
                                                    + r.status);
                                return r.arrayBuffer();
                            });
                        });
                    } else {
                        p = fetch(vurl(BASE + f.url)).then(function (r) {
                            if (!r.ok)
                                throw new Error(f.url + ": HTTP " + r.status);
                            return r.arrayBuffer();
                        });
                    }
                    return p.then(function (buf) {
                        if (f.dir) FS.createPath("/", f.dir, true);
                        FS.createDataFile(f.dir ? "/" + f.dir : "/",
                                          f.name, new Uint8Array(buf),
                                          true, true);
                    });
                }));
            }
            stage(this, "vfs");
            this._wireInput(canvas, root);
            this._wireNet();
            this._canvas = canvas;
            // SDL resolves "#canvas" via querySelector during SDL_Init
            // (inside _main): point the slot at THIS instance's canvas
            window.__autCanvasSlot = canvas;
            // _main exits via 'unwind' (emscripten_set_main_loop) or an
            // ExitStatus — both are control flow, not errors
            try { this._mod._main(0, 0); }
            catch (e) {
                if (e !== "unwind" &&
                    !(e && typeof e === "object" && "status" in e))
                    throw e;
            }
            finally { window.__autCanvasSlot = null; }
            stage(this, "main");
            load.remove();

            // pending hook calls that arrived before boot finished
            if (this._pending.task !== undefined)
                this.initializeApplication(this._pending.task);
            if (this._pending.data !== undefined)
                this.loadData(this._pending.data);
            if (this._pending.ro !== undefined)
                this.setReadOnly(this._pending.ro);
            delete this._pending;
            this.setAttribute("ready", "");   // boot finished, hooks live

            var self2 = this;
            this._poll = setInterval(function () {
                if (!self2._mod || !self2._mod.ccall) return;
                var d;
                try {
                    d = self2._mod.ccall("nkl_lua_dirty", "number",
                                         [], []);
                } catch (e) { return; }
                if (d !== self2._lastDirty) {
                    self2._lastDirty = d;
                    if (d > 0)   // boot/load bumps are not student edits
                        self2.dispatchEvent(new Event("sendDataToExternal"));
                }
            }, 250);
            this._resize(canvas);
        }

        /* canvas fills the element box; SDL sees the CSS pixel size */
        _resize(canvas) {
            var self = this;
            function apply() {
                if (!self._mod || !self._mod.ccall) return;
                var r = self.getBoundingClientRect();
                var w = Math.round(r.width), h = Math.round(r.height);
                if (w <= 0 || h <= 0) return;
                var dpr = window.devicePixelRatio || 1;
                try {
                    // web_resize resolves "#canvas" internally — point
                    // the slot at this instance first so the right
                    // element is sized
                    window.__autCanvasSlot = self._canvas;
                    try {
                        self._mod.ccall("web_resize", "void",
                                        ["number", "number"], [w, h]);
                    } finally { window.__autCanvasSlot = null; }
                } catch (e) { /* not bound yet */ }
                canvas.width = Math.max(1, Math.round(w * dpr));
                canvas.height = Math.max(1, Math.round(h * dpr));
            }
            if (typeof ResizeObserver !== "undefined") {
                new ResizeObserver(apply).observe(this);
            }
            window.addEventListener("resize", apply);
            apply();
        }

        /* in-process service loopback — same wire format as the
         * socket protocol, answered by ui_service in the same Lua
         * state (no worker, no socket) */
        _wireNet() {
            var mod = this._mod;
            var net = {
                svc: null, q: [], off: 0, ready: false,
                frame: function (text) {
                    var p = new TextEncoder().encode(text);
                    var u = new Uint8Array(4 + p.length);
                    u[0] = (p.length >>> 24) & 255;
                    u[1] = (p.length >>> 16) & 255;
                    u[2] = (p.length >>> 8) & 255;
                    u[3] = p.length & 255;
                    u.set(p, 4);
                    return u;
                },
                connect: function () {
                    if (net.ready) return 1;
                    if (!mod.cwrap) return 0;
                    try {
                        if (!net.svc)
                            net.svc = mod.cwrap("nkl_lua_service",
                                                "string", ["string"]);
                        net.ready = true;
                    } catch (e) { return 0; }
                    return 1;
                },
                state: function () {
                    if (!net.ready) net.connect();
                    return net.ready ? 1 : 0;
                },
                send: function (ptr, len) {
                    if (len < 4 || !net.svc) return -1;
                    var bytes = mod.HEAPU8.subarray(ptr + 4, ptr + len);
                    var text = new TextDecoder().decode(bytes);
                    try {
                        var reply = net.svc(text);
                        if (reply) net.q.push(net.frame(reply));
                    } catch (e) { return -1; }
                    return len;
                },
                recv: function (ptr, cap) {
                    if (!net.q.length) return 0;
                    var cur = net.q[0];
                    var n = Math.min(cap, cur.length - net.off);
                    mod.HEAPU8.set(cur.subarray(net.off, net.off + n), ptr);
                    net.off += n;
                    if (net.off >= cur.length) { net.q.shift(); net.off = 0; }
                    return n;
                },
                close: function () {
                    net.ready = false; net.q = []; net.off = 0;
                },
            };
            mod.bnNet = net;
        }

        /* hidden-input text route + key routing, scoped to the focused
         * instance via window.__autActive (several plugin elements can
         * share a page) */
        _wireInput(canvas, root) {
            var self = this;
            var input = document.createElement("input");
            input.type = "text";
            input.autocomplete = "off";
            input.spellcheck = false;
            input.setAttribute("style",
                "position:absolute;opacity:0;z-index:1000;width:1px;" +
                "height:1px;pointer-events:none;padding:0;border:none;" +
                "outline:none;background:transparent");
            root.appendChild(input);
            var sendT = null, sendC = null, sendK = null;
            function ensure() {
                if (sendT || !self._mod.cwrap) return;
                sendT = self._mod.cwrap("web_input_text", "null", ["string"]);
                sendC = self._mod.cwrap("web_input_composition", "null",
                                        ["string", "number", "number"]);
                sendK = self._mod.cwrap("web_input_key", "null",
                                        ["string", "number"]);
            }
            var inComp = false;
            input.addEventListener("compositionstart", function () {
                inComp = true; input.value = "";
            });
            input.addEventListener("compositionupdate", function (e) {
                ensure();
                if (sendC) sendC(e.data || "", 0, (e.data || "").length);
            });
            input.addEventListener("compositionend", function (e) {
                inComp = false;
                ensure();
                if (sendT) sendT(e.data || "");
                if (sendC) sendC("", 0, 0);
                input.value = "";
            });
            input.addEventListener("input", function (e) {
                if (inComp) return;
                ensure();
                if (e.inputType === "insertText" && e.data) {
                    if (sendT) sendT(e.data);
                } else if (e.inputType === "deleteContentBackward") {
                    if (sendK) { sendK("Backspace", 1); sendK("Backspace", 0); }
                } else if (e.inputType === "deleteContentForward") {
                    if (sendK) { sendK("Delete", 1); sendK("Delete", 0); }
                } else if (e.inputType === "insertFromPaste" && e.data) {
                    if (sendT) sendT(e.data);
                } else if (e.data) {
                    if (sendT) sendT(e.data);
                }
                input.value = "";
            });
            function key(e, down) {
                if (e.isComposing || e.keyCode === 229) return;
                var r = resolveKey(e);
                if (!r) return;
                if (r[1]) { e.preventDefault(); e.stopPropagation(); }
                ensure();
                if (!sendK) return;
                if (e.shiftKey && r[0] !== "Shift") sendK("Shift", 1);
                sendK(r[0], down);
            }
            input.addEventListener("keydown", function (e) { key(e, 1); });
            input.addEventListener("keyup", function (e) { key(e, 0); });

            function focusInput(x, y, kill) {
                window.__autActive = self;
                if (kill) kill.preventDefault();
                var r = root.host.getBoundingClientRect();
                input.style.left = Math.max(0, x - r.left) + "px";
                input.style.top = Math.max(0, y - r.top) + "px";
                try { input.focus({ preventScroll: true }); }
                catch (e) { input.focus(); }  // older engines: no opts
            }
            canvas.addEventListener("mousedown", function (e) {
                if (e.button !== 0) return;
                focusInput(e.clientX, e.clientY, e);
            });
            canvas.addEventListener("touchstart", function (e) {
                // iOS: the keyboard only comes up on a user-gesture
                // focus; do not preventDefault or SDL loses the touch
                var t = e.changedTouches[0];
                focusInput(t.clientX, t.clientY, null);
            }, { passive: true });

            /* Direct mouse feed: Emscripten's SDL translation resolves
             * "#canvas" through a global selector and derives positions
             * from whatever element rect it resolves to — in iframes and
             * shadow DOM that intermittently produced clamped garbage
             * coordinates and lost clicks.  Feed canvas-local positions
             * through the pending-input queue instead and starve SDL's
             * own DOM mouse handlers: our listeners are registered before
             * _main/SDL_Init, so stopImmediatePropagation blocks SDL's
             * canvas-bound handlers and prevents the event reaching its
             * document/window-level ones.  If the wasm build lacks the
             * export we keep SDL's path untouched. */
            var sendM = null;
            function nativeMouse() {
                return !!(self._mod && self._mod._web_input_mouse);
            }
            function sendMouse(x, y, btn, down) {
                if (!sendM) {
                    if (!nativeMouse()) return;
                    try {
                        sendM = self._mod.cwrap("web_input_mouse", "null",
                            ["number", "number", "number", "number"]);
                    } catch (e) { return; }
                }
                sendM(x, y, btn, down);
            }
            function localXY(e) {
                var r = canvas.getBoundingClientRect();
                return [Math.round(e.clientX - r.left),
                        Math.round(e.clientY - r.top)];
            }
            canvas.addEventListener("mousedown", function (e) {
                if (nativeMouse()) e.stopImmediatePropagation();
                var p = localXY(e);
                sendMouse(p[0], p[1], e.button, 1);
            });
            canvas.addEventListener("mousemove", function (e) {
                if (nativeMouse()) e.stopImmediatePropagation();
                var p = localXY(e);
                sendMouse(p[0], p[1], -1, 0);
            });
            canvas.addEventListener("mouseup", function (e) {
                if (nativeMouse()) e.stopImmediatePropagation();
                var p = localXY(e);
                sendMouse(p[0], p[1], e.button, 0);
            });
            canvas.addEventListener("mouseleave", function (e) {
                sendMouse(-1, -1, -1, 0);
            });
            canvas.addEventListener("pointerdown", function (e) {
                /* retarget move/up to this canvas while dragging past
                 * the element (or iframe) edge */
                try { canvas.setPointerCapture(e.pointerId); }
                catch (_) {}
            });
            canvas.addEventListener("contextmenu", function (e) {
                e.preventDefault();
            });

            /* navigation keys reach the app even when the hidden input
             * is not focused — but only while the key event actually
             * belongs to THIS element: the real target (composedPath[0];
             * e.target is retargeted to the host for shadow events)
             * must be inside our shadow tree.  An earlier version gated
             * on __autActive alone, which stays set forever after the
             * first canvas click — that swallowed every Arrow and Page
             * key on the whole exam page and killed normal scrolling.  With
             * focus on <body> or elsewhere the event passes untouched. */
            function realTarget(e) {
                var p = e.composedPath ? e.composedPath() : null;
                return (p && p.length) ? p[0] : e.target;
            }
            function outsideEditable(t) {
                return t && t !== input &&
                    (t.tagName === "INPUT" || t.tagName === "TEXTAREA" ||
                     t.tagName === "SELECT" || t.isContentEditable);
            }
            function keyIsOurs(e) {
                var rt = realTarget(e);
                if (rt === input || outsideEditable(rt)) return false;
                return rt === self || self.contains(rt);
            }
            document.addEventListener("keydown", function (e) {
                if (window.__autActive !== self) return;
                if (!keyIsOurs(e)) return;
                if (e.isComposing || e.keyCode === 229) return;
                var r = resolveKey(e);
                if (!r) {
                    if (e.key.length === 1 && !e.ctrlKey && !e.metaKey
                        && !e.altKey) {
                        ensure();
                        if (sendT) sendT(e.key);
                    }
                    return;
                }
                if (r[1]) e.preventDefault();
                ensure();
                if (!sendK) return;
                if (e.shiftKey && r[0] !== "Shift") sendK("Shift", 1);
                sendK(r[0], 1);
            }, true);
            document.addEventListener("keyup", function (e) {
                if (window.__autActive !== self) return;
                if (!keyIsOurs(e)) return;
                if (e.isComposing || e.keyCode === 229) return;
                var r = resolveKey(e);
                if (!r) return;
                ensure();
                if (!sendK) return;
                if (e.shiftKey && r[0] !== "Shift") sendK("Shift", 1);
                sendK(r[0], 0);
            }, true);
        }

        _call(name, arg) {
            if (!this._mod || !this._mod.ccall) return "";
            try {
                return this._mod.ccall(name, "string", ["string"], [arg]);
            } catch (e) {
                console.error("automata-app " + name + ":", e);
                return "";
            }
        }

        /* ---------- Anubis hooks ------------------------------------ */
        initializeApplication(arg) {
            if (!this._mod) { this._pending.task = arg; return; }
            this._call("nkl_lua_task", arg);
        }
        loadData(arg) {
            if (!this._mod) { this._pending.data = arg; return; }
            this._call("nkl_lua_load_state", arg || "");
        }
        retrieveData() {
            if (!this._mod || !this._mod.ccall) return "";
            try {
                return this._mod.ccall("nkl_lua_state", "string", [], []) || "";
            } catch (e) { return ""; }
        }
        setReadOnly(b) {
            var ro = !!b;
            if (!this._mod) { this._pending.ro = ro; return; }
            try {
                this._mod.ccall("nkl_lua_readonly", "void",
                                ["number"], [ro ? 1 : 0]);
            } catch (e) { /* bridge absent in older builds */ }
        }
    }

    if (!customElements.get("automata-app"))
        customElements.define("automata-app", AutomataApp);
})();
