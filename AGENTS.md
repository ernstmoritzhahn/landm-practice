# landm-practice — deploy repository

Generated static site (Languages & Machines practice page), built by:

```bash
python3 ~/svn/teaching/lua/stage_proof_site.py ~/svn/teaching/lua .
```

**Deploy gotcha — always `git add -A`.** The staging script writes a
`.gz` and `.br` sibling next to every `.lua` (the wasm loader fetches
`.br` first, then `.gz`, then the plain file — `ffi_engine.js
fetchText`).  Committing only the edited `.lua`/`.html` leaves stale
compressed siblings behind: the browser then runs OLD Lua code while
the plain file looks new (`curl` on the `.lua` verifies nothing —
always check the `.gz`!).  Stage, then commit the whole tree:

```bash
git add -A && git commit -m "…" && git push
```
