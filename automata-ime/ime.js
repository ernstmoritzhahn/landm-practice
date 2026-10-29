var Module = typeof Module !== 'undefined' ? Module : {};

var nklPlatform = (function() {
    var p = navigator.platform || '';
    if (/Mac|iPhone|iPad|iPod/i.test(p)) return 'mac';
    if (/Win/i.test(p)) return 'win';
    return 'linux';
})();

/* Resolve a DOM KeyboardEvent to the semantic key name the C editor sees.
 * Returns [name, shouldPreventDefault] or null for ordinary printable text.
 * Shift is handled separately by the keydown/keyup listeners so nuklear's
 * shift_mod works for selection. */
function nklResolveKey(e) {
    var p = nklPlatform;
    var isMac = p === 'mac';
    var isWin = p === 'win';
    var ctrl = e.ctrlKey, alt = e.altKey, meta = e.metaKey;

    if (e.key === 'Shift') return ['Shift', false];

    if (e.key.length === 1 && (ctrl || alt || meta)) {
        var k = e.key.toLowerCase();
        if (isMac) {
            if (meta) {
                if (k === 'a') return ['SelectAll', true];
            } else if (ctrl) {
                if (k === 'a') return ['LineStart', true];
                if (k === 'e') return ['LineEnd', true];
                if (k === 'b') return ['ArrowLeft', true];
                if (k === 'f') return ['ArrowRight', true];
                if (k === 'p') return ['ArrowUp', true];
                if (k === 'n') return ['ArrowDown', true];
                if (k === 'd') return ['Delete', true];
                if (k === 'h') return ['Backspace', true];
                if (k === 'k') return ['DeleteLineEnd', true];
                if (k === 'u') return ['DeleteLineBack', true];
                if (k === 'w') return ['DeleteWordBack', true];
            }
        } else {
            if (ctrl && k === 'a') return ['SelectAll', true];
            if (!isWin && alt) {
                if (k === 'b') return ['WordLeft', true];
                if (k === 'f') return ['WordRight', true];
                if (k === 'd') return ['DeleteWordForward', true];
                if (k === 'h') return ['DeleteWordBack', true];
            }
        }
        return null;
    }

    switch (e.key) {
        case 'ArrowLeft':
            if (isMac && meta) return ['LineStart', true];
            if (!isMac && ctrl) return ['WordLeft', true];
            if (isMac && alt) return ['WordLeft', true];
            if (!isWin && !isMac && alt) return ['WordLeft', true];
            return ['ArrowLeft', true];
        case 'ArrowRight':
            if (isMac && meta) return ['LineEnd', true];
            if (!isMac && ctrl) return ['WordRight', true];
            if (isMac && alt) return ['WordRight', true];
            if (!isWin && !isMac && alt) return ['WordRight', true];
            return ['ArrowRight', true];
        case 'ArrowUp':
            if (isMac && meta) return ['DocStart', true];
            if (isMac && alt) return ['DocStart', true];
            if (!isMac && ctrl) return ['DocStart', true];
            return ['ArrowUp', true];
        case 'ArrowDown':
            if (isMac && meta) return ['DocEnd', true];
            if (isMac && alt) return ['DocEnd', true];
            if (!isMac && ctrl) return ['DocEnd', true];
            return ['DocEnd', true];
        case 'Home':
            if (isMac && meta) return ['DocStart', true];
            if (!isMac && ctrl) return ['DocStart', true];
            return ['LineStart', true];
        case 'End':
            if (isMac && meta) return ['DocEnd', true];
            if (!isMac && ctrl) return ['DocEnd', true];
            return ['LineEnd', true];
        case 'PageUp': return ['DocStart', true];
        case 'PageDown': return ['DocEnd', true];
        case 'Backspace':
            if (isMac && meta) return ['DeleteLineBack', true];
            if (ctrl) return ['DeleteWordBack', true];
            if (!isWin && alt) return ['DeleteWordBack', true];
            return ['Backspace', true];
        case 'Delete':
            if (isMac && meta) return ['DeleteLineEnd', true];
            if (ctrl) return ['DeleteWordForward', true];
            if (!isWin && alt) return ['DeleteWordForward', true];
            return ['Delete', true];
        case 'Enter': return ['Enter', true];
        case 'Tab': return ['Tab', true];
        case 'Escape': return ['Escape', true];
    }
    return null;
}

Module.nuklearIME = (function() {
    var input = null;
    var inComposition = false;
    var ignoreNextInput = false;
    var ignoreNextData = '';
    var sendText = null;
    var sendComp = null;
    var sendKey = null;

    function ensureModule() {
        if (sendText) return;
        if (Module.cwrap) {
            sendText = Module.cwrap('web_input_text', 'null', ['string']);
            sendComp = Module.cwrap('web_input_composition', 'null', ['string', 'number', 'number']);
            sendKey = Module.cwrap('web_input_key', 'null', ['string', 'number']);
        }
    }

    function getInput() {
        if (!input) {
            input = document.createElement('input');
            input.type = 'text';
            input.id = 'nuklear-web-ime';
            input.autocomplete = 'off';
            input.spellcheck = false;
            input.style.position = 'absolute';
            input.style.opacity = '0';
            input.style.zIndex = '1000';
            input.style.width = '1px';
            input.style.height = '1px';
            input.style.pointerEvents = 'none';   // let clicks pass to the canvas
            input.style.padding = '0';
            input.style.border = 'none';
            input.style.outline = 'none';
            input.style.background = 'transparent';
            document.body.appendChild(input);

            input.addEventListener('compositionstart', function(e) {
                inComposition = true;
                input.value = '';
            });

            input.addEventListener('compositionupdate', function(e) {
                ensureModule();
                if (sendComp) sendComp(e.data || '', 0, (e.data || '').length);
            });

            input.addEventListener('compositionend', function(e) {
                inComposition = false;
                var data = e.data || '';
                ensureModule();
                if (sendText) sendText(data);
                if (sendComp) sendComp('', 0, 0);
                input.value = '';
                ignoreNextInput = true;
                ignoreNextData = data;
            });

            input.addEventListener('input', function(e) {
                if (inComposition) return;
                if (ignoreNextInput && e.data === ignoreNextData) {
                    ignoreNextInput = false;
                    ignoreNextData = '';
                    input.value = '';
                    return;
                }
                ignoreNextInput = false;
                ignoreNextData = '';
                ensureModule();
                if (e.inputType === 'insertText' && e.data) {
                    if (sendText) sendText(e.data);
                    input.value = '';
                } else if (e.inputType === 'deleteContentBackward') {
                    if (sendKey) { sendKey('Backspace', 1); sendKey('Backspace', 0); }
                    input.value = '';
                } else if (e.inputType === 'deleteContentForward') {
                    if (sendKey) { sendKey('Delete', 1); sendKey('Delete', 0); }
                    input.value = '';
                } else if (e.inputType === 'deleteWordBackward') {
                    if (sendKey) { sendKey('DeleteWordBack', 1); sendKey('DeleteWordBack', 0); }
                    input.value = '';
                } else if (e.inputType === 'deleteWordForward') {
                    if (sendKey) { sendKey('DeleteWordForward', 1); sendKey('DeleteWordForward', 0); }
                    input.value = '';
                } else if (e.inputType === 'deleteSoftLineBackward' ||
                           e.inputType === 'deleteHardLineBackward') {
                    if (sendKey) { sendKey('DeleteLineBack', 1); sendKey('DeleteLineBack', 0); }
                    input.value = '';
                } else if (e.inputType === 'deleteSoftLineForward' ||
                           e.inputType === 'deleteHardLineForward') {
                    if (sendKey) { sendKey('DeleteLineEnd', 1); sendKey('DeleteLineEnd', 0); }
                    input.value = '';
                } else if (e.inputType === 'insertFromPaste' && e.data) {
                    if (sendText) sendText(e.data);
                    input.value = '';
                } else if (e.data) {
                    if (sendText) sendText(e.data);
                    input.value = '';
                }
            });

            input.addEventListener('keydown', function(e) {
                if (e.isComposing || e.keyCode === 229) return;
                var r = nklResolveKey(e);
                if (!r) return;
                if (r[1]) {
                    e.preventDefault();
                    e.stopPropagation();
                }
                ensureModule();
                if (!sendKey) return;
                if (e.shiftKey && r[0] !== 'Shift') sendKey('Shift', 1);
                sendKey(r[0], 1);
            });

            input.addEventListener('keyup', function(e) {
                if (e.isComposing || e.keyCode === 229) return;
                var r = nklResolveKey(e);
                if (!r) return;
                if (r[1]) e.preventDefault();
                ensureModule();
                if (!sendKey) return;
                if (e.shiftKey && r[0] !== 'Shift') sendKey('Shift', 1);
                sendKey(r[0], 0);
            });
        }
        return input;
    }

    return {
        focus: function(x, y) {
            var el = getInput();
            var canvas = Module.canvas || document.getElementById('canvas');
            if (canvas) {
                var rect = canvas.getBoundingClientRect();
                el.style.left = (rect.left + x) + 'px';
                el.style.top = (rect.top + y) + 'px';
            }
            el.focus({ preventScroll: true });
        },
        blur: function() {
            var el = document.getElementById('nuklear-web-ime');
            if (el) el.blur();
        }
    };
})();

Module.preRun = Module.preRun || [];
Module.preRun.push(function() {
    var canvas = Module.canvas || document.getElementById('canvas');
    if (!canvas) return;
    canvas.addEventListener('mousedown', function(e) {
        if (e.button !== 0) return;
        var rect = canvas.getBoundingClientRect();
        var x = e.clientX - rect.left;
        var y = e.clientY - rect.top;
        // Keep focus in the hidden input so keys are still routed; prevent
        // the browser from moving focus to the canvas and stealing keys.
        e.preventDefault();
        Module.nuklearIME.focus(x, y);
    });
});

// ---- key routing -------------------------------------------------------
// The hidden input only sees keys while it is focused; navigation keys
// (arrows, Tab, Enter, ...) should reach the app regardless.  Listen on
// the document in the capture phase: special keys always go to the app,
// printable text is fed directly only when the input is NOT focused
// (otherwise the input's own 'input' event delivers it, incl. IME).
(function() {
    var sendText = null, sendKey = null;
    function ensure() {
        if (sendKey || !Module.cwrap) return;
        sendText = Module.cwrap('web_input_text', 'null', ['string']);
        sendKey = Module.cwrap('web_input_key', 'null', ['string', 'number']);
    }
    function imeEl() { return document.getElementById('nuklear-web-ime'); }

    document.addEventListener('keydown', function(e) {
        var el = imeEl();
        if (el && e.target === el) return;      // input's own listener
        if (e.isComposing || e.keyCode === 229) return;
        ensure();
        if (!sendKey) return;
        var r = nklResolveKey(e);
        if (!r) {
            if (e.key.length === 1
                && !e.ctrlKey && !e.metaKey && !e.altKey) {
                if (sendText) sendText(e.key);
            }
            return;
        }
        if (r[1]) e.preventDefault();
        if (e.shiftKey && r[0] !== 'Shift') sendKey('Shift', 1);
        sendKey(r[0], 1);
    }, true);

    document.addEventListener('keyup', function(e) {
        var el = imeEl();
        if (el && e.target === el) return;
        if (e.isComposing || e.keyCode === 229) return;
        ensure();
        if (!sendKey) return;
        var r = nklResolveKey(e);
        if (!r) return;
        if (e.shiftKey && r[0] !== 'Shift') sendKey('Shift', 1);
        sendKey(r[0], 0);
    }, true);
})();

// ---- model-server link ------------------------------------------------
// No worker and no socket here: the same Lua state that runs the UI also
// hosts the service.  ui.lua registers a ui_service global (the request
// dispatch of server/service.lua); nkl_lua_service is the C bridge that
// calls it.  send() strips the frame header, the reply is re-framed and
// queued for recv(), so the Lua side (ui/aut/net.lua) stays
// transport-agnostic — identical wire format, zero latency.
Module.bnNet = {
    svc: null,      // cwrap('nkl_lua_service') once the runtime is up
    q: [],          // inbound frames, each a Uint8Array (be32 len + json)
    off: 0,         // read offset into q[0]
    ready: false,

    frame: function(text) {
        var payload = new TextEncoder().encode(text);
        var u = new Uint8Array(4 + payload.length);
        u[0] = (payload.length >>> 24) & 255;
        u[1] = (payload.length >>> 16) & 255;
        u[2] = (payload.length >>> 8) & 255;
        u[3] = payload.length & 255;
        u.set(payload, 4);
        return u;
    },

    connect: function() {
        if (this.ready) return 1;
        if (!Module.cwrap) return 0;   // runtime not up yet; retry
        try {
            if (!this.svc) {
                this.svc = Module.cwrap('nkl_lua_service',
                                        'string', ['string']);
            }
            // an app without ui_service answers "" — still "up", the
            // client just sees error replies it already tolerates
            this.ready = true;
        } catch (e) {
            console.error('aut service:', e);
            return 0;
        }
        return 1;
    },

    // "connected" means ready.  automata's net.lua never calls
    // connect() (natively the spawned server hands over an open fd),
    // so state() connects lazily — the loopback answers as soon as the
    // runtime can cwrap the bridge.
    state: function() {
        if (!this.ready) this.connect();
        return this.ready ? 1 : 0;
    },

    send: function(ptr, len) {
        if (len < 4 || !this.svc) return -1;
        var bytes = Module.HEAPU8.subarray(ptr + 4, ptr + len);
        var text = new TextDecoder().decode(bytes);
        var reply;
        try {
            reply = this.svc(text);
        } catch (e) {
            console.error('aut service:', e);
            return -1;
        }
        if (reply) this.q.push(this.frame(reply));
        return len;
    },

    recv: function(ptr, cap) {
        if (!this.q.length) return 0;
        var cur = this.q[0];
        var n = Math.min(cap, cur.length - this.off);
        Module.HEAPU8.set(cur.subarray(this.off, this.off + n), ptr);
        this.off += n;
        if (this.off >= cur.length) { this.q.shift(); this.off = 0; }
        return n;
    },

    close: function() {
        this.ready = false;
        this.q = [];
        this.off = 0;
    },
};

// ---- responsive canvas --------------------------------------------------
// Make the Emscripten canvas fill the browser viewport without scrollbars
// or aspect distortion, and tell the C/SDL side about the new size.  The
// generated Emscripten shell has extra chrome (logo, status, output) that
// would otherwise scroll the canvas off-screen; we hide or overlay it.
(function() {
    var canvas = null;
    var viewportRef = null;

    function getCanvas() {
        if (canvas) return canvas;
        canvas = (Module && Module.canvas) || document.getElementById('canvas');
        return canvas;
    }

    function getViewportRef() {
        if (viewportRef) return viewportRef;
        var c = getCanvas();
        if (c && c.parentNode) {
            // The canvas parent is the .emscripten_border; we keep it
            // position:fixed;100% and use it as the layout reference for the
            // actual viewport size, which is more reliable than the viewport
            // APIs during fullscreen transitions.
            viewportRef = c.parentNode;
        }
        return viewportRef;
    }

    function preparePage() {
        var html = document.documentElement;
        if (html) {
            html.style.height = '100%';
            html.style.margin = '0';
            html.style.padding = '0';
        }
        var body = document.body;
        if (body) {
            body.style.height = '100%';
            body.style.margin = '0';
            body.style.padding = '0';
            body.style.overflow = 'hidden';
            body.style.background = '#000';
        }

        var c = getCanvas();
        if (c) {
            c.style.position = 'fixed';
            c.style.top = '0';
            c.style.left = '0';
            c.style.width = '100%';
            c.style.height = '100%';
            c.style.display = 'block';
            c.style.zIndex = '0';
            var border = c.parentNode;
            if (border) {
                border.style.position = 'fixed';
                border.style.top = '0';
                border.style.left = '0';
                border.style.width = '100%';
                border.style.height = '100%';
                border.style.border = '0';
            }
        }

        var hideIds = ['emscripten_logo', 'spinner', 'status', 'output'];
        for (var i = 0; i < hideIds.length; i++) {
            var el = document.getElementById(hideIds[i]);
            if (el) el.style.display = 'none';
        }

        // Hide the Emscripten shell controls: the web UI has its own
        // Nuklear-rendered fullscreen button and handles pointer visibility
        // and canvas resizing internally.
        var controls = document.getElementById('controls');
        if (controls) {
            controls.style.display = 'none';
        }
    }

    function setCanvasSize(cssW, cssH) {
        var c = getCanvas();
        if (!c) return;
        // Set the canvas to the logical CSS size we want SDL to use and a
        // backing store that matches the physical device pixels for crisp
        // rendering.  The CSS size is the viewport, so the canvas fills it.
        var dpr = window.devicePixelRatio || 1;
        c.style.width = Math.max(1, Math.round(cssW)) + 'px';
        c.style.height = Math.max(1, Math.round(cssH)) + 'px';
        c.style.display = 'block';
        c.width = Math.max(1, Math.round(cssW * dpr));
        c.height = Math.max(1, Math.round(cssH * dpr));
    }

    var lastW = 0, lastH = 0;
    function fullscreenElement() {
        return document.fullscreenElement ||
               document.webkitFullscreenElement ||
               document.mozFullScreenElement ||
               document.msFullscreenElement;
    }

    function doResize() {
        if (!Module || !Module.ccall) return;
        if (typeof Module._web_resize !== 'function') {
            setTimeout(onReady, 50);
            return;
        }
        var c = getCanvas();
        if (!c) return;
        // In fullscreen the visual viewport is the screen; in windowed mode
        // the document viewport is the browser window.  window.visualViewport
        // updates during the transition; if it isn't available or is stale,
        // fall back through the other metrics.  The .emscripten_border layout
        // box is only used as a last resort, because it may lag when an
        // element (rather than the whole document) is fullscreen.
        var w = 0, h = 0;
        if (fullscreenElement()) {
            if (window.visualViewport) {
                w = Math.round(window.visualViewport.width);
                h = Math.round(window.visualViewport.height);
            }
            if (w <= 0 || h <= 0) {
                var dpr = window.devicePixelRatio || 1;
                w = Math.round(window.screen.width / dpr);
                h = Math.round(window.screen.height / dpr);
            }
        } else {
            var ref = getViewportRef() || document.documentElement;
            var rect = ref.getBoundingClientRect();
            w = Math.round(rect.width);
            h = Math.round(rect.height);
            if (w <= 0 || h <= 0) {
                if (window.visualViewport) {
                    w = Math.round(window.visualViewport.width);
                    h = Math.round(window.visualViewport.height);
                }
            }
            if (w <= 0 || h <= 0) {
                w = Math.round(document.documentElement.clientWidth);
                h = Math.round(document.documentElement.clientHeight);
            }
            if (w <= 0 || h <= 0) {
                w = window.innerWidth;
                h = window.innerHeight;
            }
        }
        if (w <= 0 || h <= 0) return;
        if (w !== lastW || h !== lastH) {
            lastW = w; lastH = h;
            Module.ccall('web_resize', 'void', ['number', 'number'], [w, h]);
        }
        setCanvasSize(w, h);
    }

    var prepared = false;
    function onReady() {
        // Make sure we have both the runtime and the DOM before doing the
        // initial resize.  If getCanvas() is still null, we'll be called again
        // from the load event once the canvas exists.
        if (!Module || !Module.ccall) return;
        if (!getCanvas()) return;

        if (!prepared) {
            prepared = true;
            preparePage();
        }

        if (typeof Module._web_resize !== 'function') {
            // C exports are not bound yet; try again shortly.
            setTimeout(onReady, 50);
            return;
        }

        doResize();

        // onRuntimeInitialized runs before C main(), so web_resize() may be a
        // no-op at first (g_win has not been created yet).  Force a resize
        // after main() has started, so SDL_SetWindowSize actually updates the
        // logical window size to match the canvas CSS size.
        if (!Module.postRun) Module.postRun = [];
        Module.postRun.push(function() {
            lastW = 0; lastH = 0;
            doResize();
        });

        if (typeof ResizeObserver !== 'undefined') {
            var ref = getViewportRef() || getCanvas();
            var ro = new ResizeObserver(function(entries) { doResize(); });
            ro.observe(ref);
        }

        // the boot's own post-main() hook: force the canvas/window to the
        // real viewport the moment main() has installed the loop — the
        // service link can otherwise beat the first resize, leaving
        // clicks (and tests) hitting a 0.8x coordinate space
        Module.bnDoResize = function() { lastW = 0; lastH = 0; doResize(); };
    }

    var oldInit = Module.onRuntimeInitialized;
    Module.onRuntimeInitialized = function() {
        if (oldInit) oldInit();
        onReady();
    };

    window.addEventListener('resize', doResize);
    if (window.visualViewport) {
        window.visualViewport.addEventListener('resize', doResize);
    }

    ['fullscreenchange', 'webkitfullscreenchange', 'mozfullscreenchange',
     'MSFullscreenChange'].forEach(function(evt) {
        document.addEventListener(evt, function() {
            // Forget the cached size so the next doResize actually applies,
            // even if the viewport metrics briefly report the old size.
            lastW = 0; lastH = 0;
            // The browser reports the new viewport size only after the
            // transition.  Keep trying for a couple of seconds; doResize is
            // cheap and bails out when the size has not changed.
            [0, 100, 250, 500, 1000, 1500, 2000].forEach(function(t) {
                setTimeout(doResize, t);
            });
        }, false);
    });

    if (document.readyState === 'complete') {
        onReady();
    } else {
        window.addEventListener('load', function() { onReady(); });
    }
})();
