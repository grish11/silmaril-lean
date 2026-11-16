# WAST commands of the spec test suite as kernel-checked problems

A slice of the WebAssembly specification test suite, command by command, as problem rows of
the standard shapes `silmaril.shapes.wasm.wast.*`. Each row is answered by a theorem about Core
reduction (`Silmaril.Wasm.Execution.Core.Step`), checked by the Lean kernel. The same commands
were also run by a pinned independent implementation (wasmtime 50.0.0), outside CI.

Tests establish agreement only on the cases tested. A row says what silmaril-lean's Core
semantics does on one command; it does not say that the Core semantics is the specification
(see [Trust boundary](#trust-boundary)).

## The shapes

`Silmaril.Project.Shapes.WasmWast.Defs`:

| shape | Lean | statement |
|---|---|---|
| `silmaril.shapes.wasm.wast.returns` | `Returns o m pre act vs` | after the script `m`, `pre`, **some** host-free run of `act` under `profile o` reaches a normal form returning `vs` |
| `silmaril.shapes.wasm.wast.returns_only` | `ReturnsOnly o m pre act vs` | `Returns`, and **every** host-free normal form of `act` returns `vs`: no trap, no other values, no stuck or host-call state |
| `silmaril.shapes.wasm.wast.traps` | `Traps o m pre act` | some host-free run of `act` traps |
| `silmaril.shapes.wasm.wast.traps_only` | `TrapsOnly o m pre act` | `Traps`, and every host-free normal form of `act` is a trap (the trap message is not part of the claim) |

The definitions:

* `Instance m s mi`: `m` is valid (`ModuleOk m ⟨[], _⟩`, so no imports), and instantiating it
  from the empty store with `instantiateOnce?`, including the segment initialisation, gives the
  store `s`, the module instance `mi` and no start function.
* `InvokeNF o s a args c`: `c` is reachable from `$invoke(s, a, args)` by
  `Step (profile o) noHost` and has no such step.
* `Run o mi s acts s'`: each action `invoke name args` calls the function export `name` of
  `mi` and runs to an `InvokeNF` whose code is a result (values, trap or exception). Its store
  is the next state, so the store persists across calls, also after a trap.
* `ScriptAt o m pre mi s := ∃ s₀, Instance m s₀ mi ∧ Run o mi s₀ pre s`.
* `Reaches`/`Only o m pre act r`: some/every `InvokeNF` of `act` at some/every `ScriptAt` state has
  the outcome `r`.

Transfer lemmas (`….Thms`): `ScriptHolds.of_kernel` (below); `ScriptHolds.returnsOnly`,
`ScriptHolds.trapsOnly` (the row of command `k`); `ReturnsOnly.returns`, `TrapsOnly.traps`
(the weaker existence shapes); `Only.unique`, `ReturnsOnly.not_traps`,
`TrapsOnly.not_returns` (an `…_only` row excludes every other outcome).

**Profile.** `profile o` is the deterministic profile: canonical NaNs, `$ND = false`, and
`memory.grow`/`table.grow` failing exactly when the oracle `o` says so. Every row of the slice
uses `o = neverFail` (growth fails only when it must). Under `profile o`, Core reduction is
deterministic up to bubbling (`Det.DStep.join'`), so host-free normal forms are unique
(`nf_unique_of_join`). That is what makes the `…_only` shapes provable. Under the
specification profile `Profile.spec` (nondeterministic NaN payloads, relaxed SIMD, grow
failure) uniqueness does not hold and an allowed-set shape is needed. None is implemented yet.

**Termination.** A row's existence part is witnessed by the kernel run. Other runs are not
claimed to terminate, but by determinism every run that reaches a normal form reaches the same
one.

## The proof route

`ScriptHolds o m cmds` says that every command of a script holds after the commands before it.
`ScriptHolds.of_kernel (h : scriptK o fuel m cmds = true)` proves it from **one** kernel
evaluation per module (`decide +kernel`). `scriptK` validates `m` (`validate?`), checks that it
has no imports and that its function exports have scalar types, instantiates it, and runs the
commands in order with `fuel` steps each of the kernel-evaluable interpreter `runInvokeK`. For
each command it checks that the arguments are typed (`invokeOkB`), that the run stopped at a
result, and the expected outcome. The proof (`Silmaril.Proofs.Project.Shapes.WasmWast`) uses:

* `validate?_sound` and `Silmaril.Wasm.Game.IsInstance.ok`: the instantiated store is well typed;
* `runInvokeK_eq`, `runInvoke?_steps_noHost`, `runInvoke?_stopped`, `runInvoke?_sound`: the
  stopped run is a host-free normal form, and the next store is well typed;
* `Det.DStep.join'` and `nf_unique_of_join`: normal forms are unique, so a script reaches at
  most one state (`scriptAt_unique`) and every normal form of the command is the one found.

Every answer depends only on `propext`, `Classical.choice` and `Quot.sound`
(`#print axioms Silmaril.Project.WasmWast.I32.l37`, `….Traps.l17`, `….I32.script0`,
`ScriptHolds.of_kernel`).

## The slice and its counts

WebAssembly/spec at `608711107b7f1edb13efd57b7d79b49477462d36` (the archive pinned in
`tools/wasm-tools/tests/pins.sh`, SHA-256
`22ef0dd9dd9603474c6a58fa644752a3e9b887b4043d5480490290f748acda1b`):
`test/core/{i32,i64,int_exprs,fac,traps,address}.wast`. Each module is the binary that the
pinned wasm-tools 1.262.0 `json-from-wast` writes for it. The binary is read by silmaril-lean's
decoder (`decode?`, sound by `decode?_sound`), and `decodeJ : decode? bytesJ = some mJ` is
kernel-checked.

| file | commands | proved | unsupported | undetermined |
|---|---|---|---|---|
| `i32.wast` | 459 | 374 | 85 | 0 |
| `i64.wast` | 415 | 384 | 31 | 0 |
| `int_exprs.wast` | 89 | 89 | 0 | 0 |
| `fac.wast` | 7 | 6 | 1 | 0 |
| `traps.wast` | 32 | 32 | 0 | 0 |
| `address.wast` | 256 | 0 | 1 | 255 |
| **total** | **1258** | **885** | **118** | **255** |

Commands are every command after a module (`module` commands themselves are not counted). The
885 proved rows are 819 `assert_return` (`returns_only`) and 66 `assert_trap` (`traps_only`).
Reasons:

| count | status | reason |
|---|---|---|
| 255 | undetermined | `address.wast`: instantiating a data segment into a 64 KiB memory exceeds the kernel's recursion limit. The kernel evaluates the logical definition of `ByteArray.copySlice` element by element over the page; this was measured on the file's first module, and every module of the file has data segments. The native interpreter gives the expected outcome on all 255, which is not a proof. |
| 113 | unsupported | `assert_invalid`: needs validator completeness; no shape |
| 4 | unsupported | `assert_malformed` (text): no shape |
| 1 | unsupported | `assert_exhaustion` (`fac.wast`): resource exhaustion is not modelled |

No command was a mismatch, and none ran out of fuel (100 000 steps per call).

Kernel time (one `lake build` of each generated module, one core): `I32.Thms` 36 s, `I64.Thms`
43 s, `IntExprs.Thms` 33 s, `Fac.Thms` 62 s, `Traps.Thms` about 30 s.

## The oracle

`gen.py oracle` runs the pinned wasmtime 50.0.0 (`tools/wasm-jco/tests/pins.sh`, binary SHA-256
`f95e5beba6d176b447c2939607bae968ea47f87b156ddf559762f1bb3c00e9b7`) as `wasmtime wast` on one
small script per command: the same module binary as `(module binary …)`, the actions before the
command in that module, then the command. Results are in `examples/wasm-wast/oracle.json`, with
the SHA-256 of each script:

* 1140 commands run: the 885 proved ones, and the 255 of `address.wast` with a native
  interpreter observation;
* **885 of 885** kernel-proved commands pass under wasmtime, and 255 of 255 native-only ones;
* the unmodified upstream files: `int_exprs`, `fac`, `traps`, `address` pass. `i32` and `i64`
  fail on an `assert_invalid` text-parser message (`nan:arithmetic` in an `i32.const`), not on
  an execution command.

The oracle is not run in CI.

## Trust boundary

* **Core vs the specification.** Rows are about silmaril-lean's `Execution.Core.Step`. Its
  agreement with the SpecTec transcription of Wasm 3.0 is partly proved, and the whole-step
  simulation goals are open (`docs/projects/wasm.md`).
* **Instantiation** is `instantiateOnce?` (a function, related to the relational `Instantiate`
  by `instantiateOnce?_steps`).
* **Modules** must be valid, with no imports, no start function and scalar function exports.
  `register`, named modules and the spectest host are not in this fragment.
* **The binaries** are wasm-tools' output for the WAST text. The text-to-binary step is the
  pinned upstream tool's, not silmaril-lean's.
* **The generator** (`tools/wasm-wast/gen.py`) chooses which commands to give to the kernel from
  a native interpreter run. It cannot make a wrong row pass: every row is a kernel-checked
  theorem whose statement carries the module, the earlier actions, the action and the expected
  result. It can only leave commands out, and every command left out is counted with a reason
  in `examples/wasm-wast/report.json`.

## Files and how to regenerate

* `Silmaril/Project/Shapes/WasmWast/{Defs,Thms}.lean`, `Silmaril/Proofs/Project/Shapes/WasmWast.lean`:
  the shapes, the kernel checker and its soundness.
* `Silmaril/Project/WasmWast/<File>/{Defs,Thms}.lean` (generated): the bytes, modules and
  command lists, then the kernel theorems and the rows `silmaril.wasm_wast.<file>.l<line>`.
  `Silmaril.Project.WasmWast.Thms` imports them all, and `silmaril.toml` puts it in the project
  dump.
* `examples/wasm-wast/report.json` (every command: inputs, expectation, observation, status,
  reason, row), `examples/wasm-wast/oracle.json`.
* The explorer view `#/wast` (`tools/silmaril-project/src/project/explore/views/wast.js`, test
  `tests/explore/wast_view.test.mjs`) reads `wast/report.json` and `wast/oracle.json` next to
  the page, and the rows' answers from the database.

```sh
tools/wasm-tools/tests/fetch-pins.sh wasm-tools spec      # pinned, SHA-256 checked
tools/wasm-jco/tests/install.sh                           # wasmtime 50.0.0 (only for `oracle`)
python3 -I tools/wasm-wast/gen.py convert                 # wasm-tools json-from-wast
python3 -I tools/wasm-wast/gen.py probe                   # native classification (not a proof)
python3 -I tools/wasm-wast/gen.py emit                    # Lean modules and report.json
python3 -I tools/wasm-wast/gen.py oracle                  # oracle.json
lake build --wfail Silmaril.Project.WasmWast.Thms         # the kernel checks
python3 -I tools/wasm-wast/gen.py site .lake/silmaril     # report next to explore.html
```

## Not yet

NaN-pattern results (`nan:canonical`, `nan:arithmetic`) as allowed-set claims under
`Profile.spec`; `assert_invalid` (validator completeness, or a weaker validator-rejects label);
`assert_malformed` (decoder rejection); `assert_unlinkable`/`assert_uninstantiable`; imports
and the spectest host; `register`; memories with data segments in the kernel (the KMem
evaluator is the route); and the rest of the suite.
