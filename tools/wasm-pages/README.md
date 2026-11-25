# wasm-pages

`wasm-pages ARTIFACTS.toml OUTDIR` writes the data of the explorer's Wasm pages (`#/wasm`,
`#/wasm-component/…`, `#/wasm-module/…`, `#/wasm-func/…/IDX`) under `OUTDIR/wasm/`. `make pages`
runs it next to the published page.

It processes:
- the Wasm blobs of the artifact registry, those whose `meta.wasm.layer` is `module` or
  `component`;
- the core modules and nested components inside them;
- example modules that are Lean values: six of its own (including the verified LRAT and Farkas
  checkers, `Examples.LRAT.lratModule` and `Examples.Farkas.farkasMod`), and the concrete modules of the acceptor
  interpretation catalog (`Silmaril.Wasi.Accept.Catalog.concreteModules`: the verified JSON-subset
  acceptor `JsonAccept.prog`, `Game.Examples.exStart`, and the verified checkers `EmptyCheck.prog`
  and `MemberCheck.prog`).

For a Lean module the theorems are about the module value (the AST). Its bytes are encoded by
`Binaryen.Exe.encodeModule?`, which is sound for the specification's binary grammar
(`encodeModule?_sound`: `Binary.Core.Encodes bytes m`). Their SHA-256 is computed in Lean
(`Silmaril.Crypto.SHA256.digest`) over exactly the bytes written to `wasm/blob/<slug>.wasm`, and
is shown as the source's `sha256`. When exactly one registered module (`meta.wasm.layer =
"module"`) has that SHA-256, the two are one file: it is published once, as the Lean example (its
id, slug and links, `source.kind = "lean"`), with the artifact's `cid` and `path`, and the
artifact is not published again. Nothing is matched by name. The catalog modules
`JsonAccept.prog`, `exStart`, `EmptyCheck.prog` and `MemberCheck.prog` are registered this way (`examples/wasm-acceptors/`); the other
Lean examples are not registered.

Where each fact comes from, as the pages show it:

| What | How | Status |
| --- | --- | --- |
| module bytes → AST | `Binary.Core.Decode.decodeModule` | Lean, runtime |
| module validity | `Tools.Validate.check` (default features) | runtime evaluation of a validator proved equal to the specification's (`check_ok_iff`) |
| module WAT | `Tools.Text.binaryToWat` (`wasm-tools print`) | runtime; `printModule_sound` |
| function WAT | `Tools.Gen.Cmd.Print.bodyLines` on the AST | runtime, printer unverified |
| names | the `name` section; `wasm-tools demangle` in Lean | runtime |
| basic blocks, flow edges | `Cfg.blocks`, `Cfg.blockCfg` | runtime; proved to compute `Cfg.Edge` (`blockCfg_eq`, `edge_iff`), a **syntactic, incomplete** relation |
| effect marks and edges | `Cfg.blockEffects`, `Cfg.effectSucc` | runtime; syntactic "may" marks. The page draws the marks (⚠) on their blocks and the may-edges only for the selected or hovered node, or all on request; it counts every edge in its legend and lists the exact edges in the inspector. Hiding an edge from the drawing removes it from nothing else |
| block interfaces (stack in → out, local inits, labels) | `Cfg.bodyIfaces` | runtime; every recorded interface is an `Instrs_ok` derivation (`bodyIfaces_typed`) of the block's own instructions (`bodyIfaces_lookup`) |
| call graph | the call instructions of each body | syntactic; `call_indirect`/`call_ref` go to explicit unknown-callee nodes; not proved to cover the calls of any run |
| component structure | `Component.Binary.parse`, `Binary.encode` for nested components | runtime; not validated as a component |
| component WAT, WIT | `Wit.Tool.printWat`, `Wit.Tool.witText` | runtime; the WIT printer is unverified |
| dominator trees | computed in the browser on a stated basis: flow edges (the default) or flow + may-edges. Five example functions also have a kernel-checked table (`ProjectSelfTest.WasmBlockCfg`), over flow + may-edges; the page shows it as evidence only when the document has exactly this graph's nodes, entry and basis edges and its table equals the page's tree | browser, or Lean kernel-checked where linked and equal |

The page also reads the optional `model`, `bases`, `variants` and `default` fields of a body's `cfg` (issue #231), for other graphs of the same body, and per graph `granularity` (`"block"`, or `"instr"` with `nodes: [[block, position]]`, drawn boxed by block) and `outcomes: [[node, effect, handler?]]` (effects that are not edges, such as trap and raise in an all-effects model; a handler is a node, `"caller"` or `"unresolved"`; outcomes are in no dominator basis). A variant with its own `blocks` may give `members: [[block index of the shared numbering]]` per block (e.g. maximal basic blocks); the page links each such block to its members and back, and never merges blocks itself. `wasm-pages` writes none of them yet; the page draws a variant exactly as given, and shows its `relation` as metadata, not as a proof.

Nothing on these pages claims that an execution follows a drawn graph. Semantic properties
(trap, divergence, determinism) are shown only as open statements.

## Pinned SQLite reactor pilot

The optional `--sqlite-reactor` argument accepts the stripped WASI Preview 1
reactor produced by the checked SQLite build. The normal Pages workflow
continues to use the two-argument invocation. The pilot reads the digest and
version from `tools/sqlite-wasm/reactor.json`, checks the actual artifact bytes,
and runs the ordinary Core decoder. A digest mismatch or module decode failure
aborts the opt-in build. A module decode failure leaves per-function counts
unavailable.

```sh
bash tools/sqlite-wasm/build.sh "$ARCHIVES" "$WORK/sqlite3.wasm" "$WORK/sqlite3.map"
make pages
.lake/build/bin/wasm-pages silmaril/artifacts.toml _site --sqlite-reactor "$WORK/sqlite3.wasm"
python3 -B tools/wasm-pages/check-sqlite-reactor.py _site "$WORK/sqlite3.wasm" "$WORK/sqlite3.map"
node tools/silmaril-project/tests/explore/sqlite_reactor.mjs _site "$WORK/shots"
```

The build keeps the full import-first function index and runs `Cfg.blockCfg`
on every definition. It counts an explicit `Cfg.Target.invalid` as an
unsupported target. The module shows those counts separately from the number
of published detail files. Detail is limited to the initialization, version,
and four varint pilot slots, with a 600-instruction limit per function. The
page fetches those CFGs by slot. Whole-module validation, WAT and call-graph
extraction are outside the pilot. The graphs describe syntactic relations.
The quoted reactor's existing `SqliteWasm.originalDecode` theorem concerns
whole-module decoding at the pinned original bytes.

Internal C names are selected linker-map annotations. The verifier uses the
same pinned build to compare all framed Code body sizes and offsets with the
map before checking the four names. The Wasm import and export names come
from the module decoder. Proof links identify specific existing Lean
statements. A name match alone gives no source, IR, or semantic correspondence.

The generator also reads the [LLVM build receipt](../sqlite-wasm/llvm-provenance/receipt.json)
when the reactor is enabled. Each linked row must match the reactor digest,
import-first slot, and original Code frame offset and length. The name must
agree with the decoded export or the C annotation. The page's source
metadata supplies the receipt's Git revision.
The function page shows the early bitcode symbol and digest under
“LLVM build provenance”. The receipt records build stages and symbol
associations. The Lean links continue to identify their own statements.

The following check generates a default site and opt-in receipt controls in
a fresh directory. It changes the exported version getter's offset and
length independently and together while preserving its name, digest and slot.

```sh
python3 -B tools/wasm-pages/check-sqlite-llvm-links.py \
  .lake/build/bin/wasm-pages "$WORK/sqlite3.wasm" "$WORK/receipt-controls"
```

After adding the Explorer page and project database to a generated site, run
`sqlite_reactor.mjs` against it. For a bad-export control, set
`SQLITE_REACTOR_LLVM_289=absent` and `SQLITE_REACTOR_LLVM_530=present` to
check that the version getter keeps its Lean link and lazy CFG, and that the
writer still links to the receipt.
