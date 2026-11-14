# wasm-pages

`wasm-pages ARTIFACTS.toml OUTDIR` writes the data of the explorer's Wasm pages (`#/wasm`,
`#/wasm-component/…`, `#/wasm-module/…`, `#/wasm-func/…/IDX`) under `OUTDIR/wasm/`. `make pages`
runs it next to the published page.

It processes:
- the Wasm blobs of the artifact registry, those whose `meta.wasm.layer` is `module` or
  `component`;
- the core modules and nested components inside them;
- four example modules that are Lean values.

Where each fact comes from, as the pages show it:

| What | How | Status |
| --- | --- | --- |
| module bytes → AST | `Binary.Core.Decode.decodeModule` | Lean, runtime |
| module validity | `Tools.Validate.check` (default features) | runtime evaluation of a validator proved equal to the specification's (`check_ok_iff`) |
| module WAT | `Tools.Text.binaryToWat` (`wasm-tools print`) | runtime; `printModule_sound` |
| function WAT | `Tools.Gen.Cmd.Print.bodyLines` on the AST | runtime, printer unverified |
| names | the `name` section; `wasm-tools demangle` in Lean | runtime |
| basic blocks, flow edges | `Cfg.blocks`, `Cfg.blockCfg` | runtime; proved to compute `Cfg.Edge` (`blockCfg_eq`, `edge_iff`), a **syntactic, incomplete** relation |
| effect marks and edges | `Cfg.blockEffects`, `Cfg.effectSucc` | runtime; syntactic "may" marks |
| block interfaces (stack in → out, local inits, labels) | `Cfg.bodyIfaces` | runtime; every recorded interface is an `Instrs_ok` derivation (`bodyIfaces_typed`) of the block's own instructions (`bodyIfaces_lookup`) |
| call graph | the call instructions of each body | syntactic; `call_indirect`/`call_ref` go to explicit unknown-callee nodes; not proved to cover the calls of any run |
| component structure | `Component.Binary.parse`, `Binary.encode` for nested components | runtime; not validated as a component |
| component WAT, WIT | `Wit.Tool.printWat`, `Wit.Tool.witText` | runtime; the WIT printer is unverified |
| dominator trees | computed in the browser; five example functions also have a kernel-checked table (`ProjectSelfTest.WasmBlockCfg`) | browser, or Lean kernel-checked where linked |

Nothing on these pages claims that an execution follows a drawn graph. Semantic properties
(trap, divergence, determinism) are shown only as open statements.
