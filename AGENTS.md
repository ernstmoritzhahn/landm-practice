# landm-practice — deploy repository

Generated static site (practice pages for L&M and Advanced Logic),
built from MULTIPLE source roots — shared tooling in teaching/lua,
course modules in the course repos:

```bash
python3 ~/svn/teaching/lua/stage_proof_site.py \
    ~/svn/teaching/lua ~/svn/advanced-logic/lua ~/svn/l-and-m/web .
```

Each root carries its own `modules.json` fragment; the script merges
them (a module defined by two roots errors out) and writes the merged
manifest as `modules.json`.

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
