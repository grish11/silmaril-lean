# Component tests: instantiation-time behaviour of component binaries

Two real component binaries, assembled by a pinned tool, whose behaviour **at instantiation** is
stated by reusable problem shapes and proved in Lean over the bytes; the reference machine runs
the component the existing decoder `Conformance.decodeRef` reads from the same bytes (kernel-checked
on these two binaries), and wasmtime is run on the same bytes as an independent oracle.

## The binaries

`examples/component-tests/{starts,trap}.wat`, assembled by the pinned `wasm-tools` 1.262.0
(`tools/wasm-tools/tests/pins.sh`, SHA-256 checked) with `parse`, `strip --all` (no name
sections) and `validate`. `tools/component-tests/build.sh` reproduces the committed `.wasm` files
byte for byte (`--write` rewrites them). Lean reads them with `include_bytes`
(`Silmaril.Wasm.Component.InstTests.startsBytes`, `trapBytes`).

| binary | size | SHA-256 | content |
|---|---|---|---|
| `starts.wasm` | 256 B | `ff543e05…02665f` | imports `f: func(x: u32)`; core instances, in order: `call1` (start: `f(1)`), `call2` (start: `f(2)`), `glob` (start: a mutable global, initially `0`, set to `42`); exports `get: func() -> u32` (`canon lift` of `glob`'s `get`, which reads the global) |
| `trap.wasm` | 188 B | `1cccda32…649d20` | imports `f`; core instances: `trap` (start: `unreachable`; exports `get` returning `7`), then `call2` (start: `f(2)`); exports `trap`'s `get` |

The same directory holds two more binaries, assembled the same way: not tests of
instantiation-time behaviour but regressions of the decoder bridge (see
[the bridge evidence](#component-bridge-evidence-the-two-readings-of-a-binary)):
`instexport.{wat,wasm}` (an exported instance, on which the two readings name different
exports) and `paramname.{wat,wasm}` (256 B, SHA-256 `347583e4…3113da2`: `starts` with the import
declared `f: func(y: u32)`, a counterexample to `Task.startAdequacy`). They have no rows and no
oracle run.

`f` reaches the core instances through `canon lower`, `get` leaves through `canon lift`, so the
import trace is observed in component values: `f(u32 1)`, answered `()`.

## Semantics and assumptions

* **Path.** `Binary.parseComponent` (the verified parser, then the partial lowering to the
  component IR, `Comp Binary.CoreMod`), then the instantiating denotation `Comp.denI` over
  `Binary.coreModSemI P`: each core module is decoded and run on the Core 3.0 engine at profile
  `P`, its start function **at instantiation** (its import calls are moves of the instantiation
  phase; a trap fails it), and core instances are instantiated in program order; a failure is the
  answer of the whole instantiation and later instances are never started. This is
  `Silmaril.Wasi.Accept.componentBytesSystemCore3I P` before its export phase (`Comp.denX`).
* **Profiles.** Existence statements give a play at **every** profile `P`. Exclusion statements
  are about **every** play at **every deterministic profile** `profile o` (every `GrowOracle o`).
* **Finite plays.** Plays are finite; a start function or export call that never returns makes no
  move. **Divergence is not observed**: an exclusion statement constrains the moves that happen.
  (At `profile o` the start runs of these modules reach their normal forms, but that is not part
  of the statements.)
* **Host.** The host is a function answering each import call; the rows use the typed host
  `unitHost` (`f` answered `()`). The clauses about which import calls happen hold whatever the host
  answers; the clauses about outcomes (`ready`, export answers) assume the host answers as given.
* **No async, resources, streams or futures**: the lowering rejects them.

## Shapes

`Silmaril/Project/Shapes/ComponentTest/{Defs,Thms}.lean`. Each takes the bytes `b`; each states
that `b` lowers to some `c` (`Binary.parseComponent b = .ok c`) and then:

| name | Lean | statement about `c` |
|---|---|---|
| `silmaril.shapes.component.test.instantiates` | `Instantiates b host tr` | `tr` is answered by `host`; at every profile `[inst] ++ tr ++ [ready]` is a play; at every deterministic profile the import calls of every play are a prefix of `tr`'s, and a complete instantiation answered by `host` is exactly `tr` followed by `ready` |
| `silmaril.shapes.component.test.inst_traps` | `InstTraps b host tr` | at every profile `[inst] ++ tr ++ [fail ()]` is a play; at every deterministic profile the import calls of every play are a prefix of `tr`'s, and no play answered by `host` contains `ready` or an export answer |
| `silmaril.shapes.component.test.export_returns_after_inst` | `ExportReturnsAfterInst b host tr q v` | at every profile `[inst] ++ tr ++ [ready, q?, v!]` is a play; at every deterministic profile every answer to `q` in a play answered by `host` is `v` |

Consequences (`Thms`): `Instantiates.unique`, `InstTraps.not_ready`, `InstTraps.no_exports`,
`InstTraps.no_calls` (empty trace: no import call at all), `ExportReturnsAfterInst.denX` (the
answer in the export phase), `ExportReturnsAfterInst.instantiates_play`.

## Rows and theorems

`Silmaril/Project/ComponentTests/{Defs,Thms}.lean`, in the group `silmaril.component_tests`
(under `silmaril.all`). All three are proved (`@[solves]`).

| row | shape | statement |
|---|---|---|
| `silmaril.component_tests.starts.instantiates` | `instantiates` | `starts.wasm`, `unitHost`, trace `[f(u32 1) ↦ (), f(u32 2) ↦ ()]` |
| `silmaril.component_tests.starts.get_after_inst` | `export_returns_after_inst` | `starts.wasm`, that trace, `get()` ↦ `u32 42` |
| `silmaril.component_tests.trap.inst_traps` | `inst_traps` | `trap.wasm`, `unitHost`, empty trace |

They come from `Silmaril.Wasm.Component.InstTests.Thms` (proofs in
`Silmaril/Proofs/Wasm/Component/InstTests/`):

* **Bytes.** `parse_starts`, `parse_trap`: the bytes lower to the literal components
  `startsComp`, `trapComp` (one definitional check by the kernel, `kernel_rfl`); the core decoder
  reads the embedded modules as the litmus modules of `InstLitmus` (`coreModule_*`), so
  `startsComp.denI (coreModSemI P) = startsC.denI (core3SemI P)` (`Transfer`).
* **Existence** (`Pos`): the plays are assembled node by node from Core 3.0 start runs built from
  `Step` rules and instances computed by `decide +kernel` (`InstLitmus`), through the `canon
  lower`/`canon lift` wiring (`lowF_runs`, `getL_runs`).
* **Exclusion** (`Det`): at `profile o` each module is bounded by a script (`callMod_le_script`,
  `trapMod_le_script`, and the new `globMod_le_script`: `inst` → `ready`, `get()` → `42`, by a
  simulation using the uniqueness of normal forms); so the components are bounded by handlers
  whose programs are computed by reduction. Generic handler facts: `handler_ans_pure`,
  `runs_of_instPlay`, `runs_host_unique`, `mem_ofHandler_of_guard`.

`starts_get` gives the component-level uniqueness of the export answer at deterministic profiles,
which `InstLitmus` leaves open for `globC`/`callGlobC` (only the module-level `globMod_get_det`
is there).

`#print axioms` of every answer theorem: `[propext, Classical.choice, Quot.sound]`.

## The reference machine (these two examples only)

`Silmaril.Wasm.Component.InstTestsRef`. The REF side reads the bytes through the existing route
`Conformance.decodeRef` (`Binary.parse`, the verified component grammar, then `Conformance.toRef`,
which decodes the embedded core modules with the core decoder); no new decoder is introduced.

* `decodeRef_starts`, `decodeRef_trap`: `decodeRef startsBytes = .ok startsRef` and
  `decodeRef trapBytes = .ok trapRef`, one definitional check by the kernel (`kernel_rfl`).
  `startsRef` and `trapRef` are spelled out in `InstTestsRef.Defs` only so that they can be read.
* `starts_valid`, `trap_valid`: `∃ ct, Valid Features.p2 c ct` (`decide +kernel` on `check?`, then
  `check?_sound`), so `Wasi.Accept.Ref.decodeValid` accepts both binaries.
* `starts_agree P`: the IR play above, and `∃ c, decodeRef startsBytes = .ok c`, `c` valid, and the
  reference machine under the logging host instantiates `c` with the host log `f(1)`, `f(2)`
  (`logOfCalls startsTrace`) and then answers `get()` with `u32 42`.
* `trap_agree P`: the IR instantiation fails, and `∃ c, decodeRef trapBytes = .ok c`, `c` valid,
  and the reference machine's instantiation of `c` traps.

The reference side is one executed run each (`decide +kernel` on the session driver and on a trap
summary, then their soundness theorems), with the Core 3.0 stepper of `core3 neverFail` and the
first scheduling oracle. The host function has the type the binaries import, `func(x: u32)`
(`hostConfigX`): the reference machine compares parameter names when it links an import, and the
generic `LinkedSession.hostConfig hostI` names the parameter `a`, so the decoded components do not
link against it.

What this covers, and what it does not:

* Both sides start from the same bytes, through two readings: `Binary.parseComponent` (the IR's
  lowering) and `decodeRef` (the reference syntax). They share the parser and agree on core
  instantiations for every binary (next section); behavioural agreement is shown only on these
  two binaries, by running both.
* `toRef` is the conformance runner's executable reading of `Binary`; no theorem relates it to the
  reference's own reading of `Binary.md`.
* No general adequacy between `Comp.denI` and the reference machine is claimed.

## Component bridge evidence: the two readings of a binary

`Silmaril.Wasm.Component.DecoderBridge` (`Defs`, `Thms`; proofs in
`Silmaril.Proofs.Wasm.Component.DecoderBridge`).

| level | what agrees | for which binaries | status |
|---|---|---|---|
| structural | core modules (decoded from the same bytes) and the order of core instantiations (`rel_of_decode`) | every binary both readings accept | **proved** |
| wiring and types | imports, exports (names, types, lift/lower chains), each node's module interface and the wiring its arguments name (`relW_of_decode`) | every binary both readings accept whose REF reading is in `InFrag` (decidable) | **proved** |
| exported instances | the IR names `i#get`, the reference machine has no function export of that name (`DecoderBridge.InstExport`) | `instexport.wasm` | **mismatch demonstrated** (kernel runs); outside `InFrag` |
| parameter names | the IR drops them (`paramname.wasm` reads as `startsComp`); the reference root check compares them and traps on every run, so `Task.startAdequacy` is false (`DecoderBridge.not_startAdequacy`); the decidable certificate `RootChecked` (the reference's own root checks) fixes the domain: outside it the reference traps and has no run (`traps_of_not_rootChecked`, `not_instantiates_of_not_rootChecked`); `starts.wasm` passes it (`starts_rootChecked`), `paramname.wasm` does not (`not_rootChecked_paramName`) | every binary both readings accept | **counterexample proved**; corrected goal `Task.startAdequacyChecked` open; `MultiImpFrag` passes the certificate (`rootChecked_of_multiImpFrag`) |
| behaviour, IR half | an IR instantiation play is node by node: each core node's own instantiation play, down to its core engine run (`InstWired.nodesInst_of_denI`, `NodesInst.fail_nil`, `coreNodeI_engine_nil`) | every binary both readings accept whose REF reading is import-wired (`HostWired`, decidable: in `InFrag`, every core instantiation's imports wired to the component's imports), for failing instantiations and for the instantiation part of start plays (`DecoderBridge.Sim`) | **proved** |
| behaviour, reference half, first core node | a quiet failure of IR core node `0` (preparation fails, or the start function traps without an import call) makes the reference machine's instantiation trap, by a symbolic run of the machine (`DecoderBridge.firstCore_fail_ref`) | every import-wired binary in the first-core fragment (`FirstCoreFrag`, decidable: types, function imports, core modules, `canon lower`, inline core instances before the first core instantiation; its module without imports, memories, tables, tags or segments); `trap.wasm` is (`trap_firstCoreFrag`), `starts.wasm` is not | **proved** (`trap_of_firstCore`: the REF half of `trap.wasm` from the IR run, no hypothesis) |
| behaviour, reference half, first core node with lowered imports | a quiet failure of IR core node `0` whose module imports exactly the `canon lower` trampolines of `f` defined before it makes the reference machine trap (`DecoderBridge.firstImp_fail_ref`); so does a failure **after host calls** (`firstImp_failCalls_ref`, node outcome `NodeCalls`); a node that is ready after host calls `t` brings the reference machine to the return of its start function with the host log `logOfCalls t`, or it traps earlier, or `t = []` (`firstImp_ready_ref`) | every import-wired binary importing `f: func(u32)` in the decidable fragment `FirstImpFrag` (the first module's imports resolve, in order, to the `canon lower`s before it, at core type `(func (param i32))`); `starts.wasm` is (`starts_firstImpFrag`), `trap.wasm` is not (it is in `FirstCoreFrag`) | **proved**, given the node outcome (`NodeQuiet`, `NodeCalls`); `NodeCalls` is derived from the IR play on `MultiImpFrag` (`nodeCallsIR`, next row) |
| behaviour, start goal on several core instantiations | `Task.startAdequacy` restricted to the decidable fragment `MultiImpFrag` (`Task.startAdequacyFrag`) follows from three pieces (`startAdequacyFrag_of_nodes`): (a) `Task.nodeCallsIR`, the IR play of a ready instantiation splits into each node's calls as `NodeCalls` (**proved**, `nodeCallsIR`); the instantiation `Task.nodesRef` (pieces (b) and (c) together): the reference machine runs the root checks, the first core instantiation with its start function, host calls and start epilogue, the **later core instantiations in the shared core store** (each node's IR store mapped into it, its imports kept at the trampolines and its own objects moved past the earlier instances: `Gap.rel`) and the other definitions, and finishes the instantiation with the host log `logOfCalls ts.flatten` (**proved**, `nodesRef`); (d) `Task.exportRef`, the first export (`canon lift`, `func() -> u32`) answers as the IR's does | binaries in `MultiImpFrag` (decidable: `FirstImpFrag`, `HostWired`, every node's imports of core type `(func (param i32))` wired to the lowering of `f`, the root starts with `type func(x: u32)` and `import f` and imports nothing else, later definitions are split-fragment core instantiations of modules importing only functions, the trampolines in order at accepting types, primitive types, core export aliases into modules with distinct export names, option-less lifts and function exports, first export of type `func() -> u32`); `starts.wasm` is (`starts_multiImpFrag`) | (a), (b)+(c) **proved**; (d) **open**: `startAdequacyFrag_of_d : Task.exportRef → Task.startAdequacyFrag`, `starts_of_d` (the REF half of `starts.wasm` from the IR run, given (d)) |
| behaviour, reference half, later failing node | node `k ≥ 1` fails quietly after quiet ready nodes: the reference instantiation traps (`LaterFail.laterFail_ref`) | binaries in `MultiImpFrag` | **proved** (`failRefWiredRest'_of_rest'' : Task.failRefWiredRest'' → Task.failRefWiredRest'`) |
| behaviour, reference half, other cases | node `k ≥ 1` fails outside `MultiImpFrag`, or binaries outside `FirstCoreFrag' = FirstCoreFrag ∨ FirstImpFrag` | none | **open** (`Task.failRefWiredRest''`; `failRefWiredRest_of_rest'`, `failRefWired_of_rest'` and `failAdequacyWired_of_rest'` proved; `Task.failRefWiredRest` and `Task.failRefWired` unchanged and open) |
| behaviour | `Comp.denI` (IR) against the reference machine's instantiation and sessions | none in general; `starts`/`trap` by execution of both machines | **open** (`Task.failAdequacy`, `Task.startAdequacy`; `Task.failAdequacyWired` on import-wired binaries; on `MultiImpFrag`, `Task.startAdequacyFrag` reduced to `Task.exportRef`) |

**How the two readings are built.**

| | IR reading | REF reading |
|---|---|---|
| entry point | `Binary.parseComponent : ByteArray → Except String (Comp Binary.CoreMod)` (`Binary/Lower/Defs.lean`) | `Conformance.decodeRef : ByteArray → Except String Core3Component` (`Conformance/ToRef/Defs.lean`) |
| parser | `Binary.parse` (the verified component grammar) to `Binary.Ast` | the same `Binary.parse` |
| AST to output | `Binary.lower`: a state-passing pass (`Lower.St`, `Lower.section_`) resolving indices into the nested IR (`Comp.mk imports nodes exports`) | `Conformance.toRef`: a section-by-section transcription into the reference syntax (`Syntax.Definition`) |
| embedded core modules | `Lower.coreMod`: the core decoder `Wasm.Binary.Core.decode?`, keeping the bytes and the function interface (`Binary.CoreMod`) | `ToRef.coreModule`: the same `decode?`, keeping the decoded `Wasm.Module` |
| core `instantiate m args` | an IR node `.core m wiring`, the wiring resolved by name through the argument instances | kept as `.coreInstance (.instantiate m args)` |

**Proved for every byte string** (`#print axioms`: `[propext, Classical.choice, Quot.sound]`):

* `decoders_factor`: `parseComponent b = .ok c → decodeRef b = .ok r →
  ∃ a, Binary.parse b = .ok a ∧ Binary.lower a = .ok c ∧ toRef a = .ok r`.
* `lower_nodes`: `Binary.lower a = .ok c →` the nodes of `c` correspond one to one, in order, to
  `instExprs a.sections` (the top-level core instantiations), each `.core m w` with
  `Lower.coreMod bs = .ok m` for `bs` the bytes of the core module section at the instantiation's
  index (`modBytes a.sections`); and `noModuleSort a.sections` (no top-level import, alias or
  export of the core module sort). `coreMod_bytes`: such an `m` has `m.bytes = bs` and `decode?`
  accepts `bs`.
* `toRef_insts`: `toRef a = .ok r → noModuleSort a.sections →
  coreModSpace r = (modBytes a.sections).map decode? ∧ refInsts r = instExprs a.sections`.
* `rel_of_decode`: `parseComponent b = .ok c → decodeRef b = .ok r → Rel c r`, where `Rel c r` is
  `List.Forall₂ (NodeRel (coreModSpace r)) c.nodes (refInsts r)` and `NodeRel space n (i, args)`
  is `∃ m w ref, n = .core m w ∧ space[i]? = some (some ref) ∧ decode? m.bytes = some ref`: the
  same core modules, decoded from the same bytes, are instantiated in the same order.
* `starts_rel : Rel startsComp startsRef`, `trap_rel : Rel trapComp trapRef`: instances of
  `rel_of_decode` (from `parse_starts`/`parse_trap` and `decodeRef_starts`/`decodeRef_trap`;
  no new kernel run).

`Rel` is structural: which core modules are instantiated, in which order, from which bytes.
Neither reading's success implies the other's.

**Wiring, imports and exports, in a fragment** (`DecoderBridge.Wire`; proofs in
`Silmaril.Proofs.Wasm.Component.DecoderBridge.Wire`; `#print axioms`:
`[propext, Classical.choice, Quot.sound]`).

* `refRead r : Option RSt` reads the wiring a reference component names: a fold over its
  definitions that resolves the index spaces the reference machine's instantiation builds
  (`Instantiate.instantiateDef`), symbolically: each component function, core function and core
  instance is the IR wiring program (`Impl`) it denotes over the IR environment (imports, then
  the core instances' function exports), and each core instantiation's imports are resolved by
  name through its arguments (`List.lookup`, the first match, as `Instantiate.coreImportFor?`).
* `InFrag r` (decidable, `inFrag r = true`): `refRead r` succeeds. The fragment: top-level
  definitions only, among core modules whose imports are all numeric functions; function types
  over primitive non-string types (at most 16 flat parameters, 1 flat result, synchronous);
  function imports; core instantiations and inline core instances of core functions; aliases of
  core function exports; `canon lift`/`canon lower` without options, `lower` only of a function
  that is not a lifted one; function exports without type ascription. No instance imports or
  exports, nested components, component instances, values, start definitions, resources or
  built-ins.
* `relW_of_decode`: `parseComponent b = .ok c → decodeRef b = .ok r → InFrag r → RelW c r`, where
  `RelW c r` says: `refRead r = some R`, `c.imports = R.imports`, `c.exports = R.exports` (names,
  types, and the `lift`/`lower` chains with their targets), and node `k` of `c` is `.core cm w`
  where `cm`'s bytes decode to the module of instantiation `k` of `r`, `cm`'s interface is that
  module's (`coreIface`, what `Lower.coreMod` reads), and `w` is the wiring the instantiation's
  arguments name.
* `starts_inFrag`, `trap_inFrag` (`decide +kernel`), `starts_relW`, `trap_relW`.

This is syntax: both readings name the same wiring. That the reference machine's run follows
`refRead`, and any behaviour, is not proved.

**A demonstrated mismatch outside the fragment: exported instances** (`DecoderBridge.InstExport`,
`examples/component-tests/instexport.{wat,wasm}`, 117 B, SHA-256 `8ba16937…2039c5`). The binary
imports `f` (unused), lifts a core `get` returning `42`, and exports it through an inline
instance `i`. The IR reading flattens the exported instance to an IR export named `i#get`
(`parse_instExport`, `instExport_ir_exports`); the REF reading keeps the instance export `i`
(`decodeRef_instExport`, valid: `instExport_valid`; `instExport_not_inFrag`), and the reference
machine reports the root instance's **function** exports only: on an executed run under the
logging host it reports none (`instExport_ref_run`, `decide +kernel` on `instantiateRun`), so
the IR's export name `i#get` is not found. This is why `Task.startAdequacy` now assumes `InFrag`;
it is not a proof of the negation of the first statement (that needs the IR's answer to `i#get`
and the absence of `i#get` from **every** reference run). Flattened names cannot collide with
top-level export names of valid components (`#` is not in an extern name; `wasm-tools` rejects
an export `i#get`). Comparing functions of exported instances needs a reference export-path
lookup (`i`, then `get`), which the session relation `sessRunFrom` does not have: open.

**Open, stated as `Prop`s** (`DecoderBridge.Sem.Defs`; no theorem asserts them): the semantic
equivalence of the two readings is **entirely unproved** beyond the executed examples.

* `Task.failAdequacy`: for every binary importing exactly `f: func(u32)` whose REF reading is
  valid, an IR instantiation (at `profile neverFail`) failing before any host call implies
  `InstResult.traps` on the reference machine under the logging host (`embL`, `hostConfigX`).
* `Task.startAdequacy`: for such a binary whose REF reading is in the fragment (`InFrag r`; the
  first statement had no fragment hypothesis, see above), an IR play
  `instPlay t .ready ++ [get(), ws]` (each host call answered `()`) implies the REF session from
  `hostConfigX` with host log `logOfCalls t` and the first export (by name) returning
  `ws.map toRefVal`. **False** (`DecoderBridge.not_startAdequacy`, `paramname.wasm`); the
  corrected goal is `Task.startAdequacyChecked`, with the root certificate `RootChecked`.

**The IR half, on import-wired binaries** (`InstWired`, `DecoderBridge.Sim`; proofs in
`Silmaril.Proofs.Wasm.Component.InstSem.{Unzip,Wired,WiredEngine}` and
`Silmaril.Proofs.Wasm.Component.DecoderBridge.Sim`; `#print axioms`:
`[propext, Classical.choice, Quot.sound]`).

* `Unzip` (generic, every signature): a play of a composite made of complete rounds is made of
  complete rounds of the upper strategy, each served by consecutive complete rounds of the lower
  one (`zip_rounds_inv`, the converse of `zip_round`); complete rounds of a handler run its
  programs; complete rounds of a pairing and of copycat likewise.
* `InstWired.nodesInst_of_denI` (every core semantics `C`): in an import-wired component
  (`ImportWired I.length ps`: every core node's wiring calls only the imports, so no core
  instance calls another), every instantiation play `instPlay cs a` of
  `Comp.denI C (Comp.mk I (coreNodes ps) xs)` is `NodesInst C I.length ps cs a`: the nodes
  instantiate in program order, node `k` only after the nodes before it are ready, each node's
  own play `instPlay w' a' ∈ coreNodeI C I.length m args` contributing its calls `w'` to `cs`;
  the first failure is the answer.
* `NodesInst.fail_nil`: a failure without calls fails at one node `k`, the nodes before it ready,
  each without a call. `coreNodeI_engine_nil`: at an engine semantics (`Binary.coreModSemI` is
  one), such a node play is a run of the module's engine instance (`EngineInst`: no instance, no
  start function, or a start run `Param.StartRunI` returning or trapping), its import calls
  answered at once by the wiring.
* `DecoderBridge.HostWired r` (decidable): `refRead r = some R` and every core instantiation's
  wiring in `R` calls only the component's imports (`starts_hostWired`, `trap_hostWired`, by
  `decide +kernel`). With `relW_of_decode`, the IR reading of such a binary is import-wired
  (`wired_of_decode`, in the proofs).
* `DecoderBridge.failAdequacyWired_of : Task.failRefWired → Task.failAdequacyWired`, where
  `Task.failAdequacyWired` is `Task.failAdequacy` with the hypothesis `HostWired r`, and
  `Task.failRefWired` (**open**) is its reference half: if the core engine runs of the decoded
  modules make the nodes before `k` ready and node `k` fail, each without a host call
  (`NodeQuiet`), the reference machine's instantiation traps. `trap_of_wired`: the trap example
  from `Task.failRefWired`.
* `DecoderBridge.FirstCore` (proofs in `Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore`;
  `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`): **the case `k = 0` of
  `Task.failRefWired`**, `firstCore_fail_ref`, on every import-wired binary in the decidable
  first-core fragment `FirstCoreFrag`. The reference machine is run symbolically: root
  instantiation up to the first core instantiation traps on a bad import or runs silently,
  allocating host functions in the core store (`Prefix`, `Root`, over any engine); the
  reference preparation of the module in that store is the IR's preparation alone, relocated
  (`CoreSim.prepareE_shift`); its failure traps `coreTrap`; otherwise the start call reaches the
  core activation (`Path.start_coreG`, over any engine and host state), and the IR's run of the
  start function to a trap, relocated (`steps_shift`), is matched by the concrete engine's
  interpreter run in the machine (`CoreRun.runCI_complete`, `lrun_coreTrap`). The remaining
  cases are `Task.failRefWiredRest` (**open**: node `k ≥ 1`, or outside the fragment);
  `failRefWired_of_rest` proved. `trap_of_firstCore`: the reference half of `trap.wasm` from the
  IR's run of its first node (`trapCM_nodeQuiet`), with no hypothesis.
* `DecoderBridge.FirstImp` (proofs in `Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp`;
  `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`): **the first core instantiation
  with lowered imports**, on import-wired binaries importing `f: func(u32)` in the decidable
  fragment `FirstImpFrag` (`starts.wasm` is in it). The definitions before the first core
  instantiation run to the core store of `n` trampolines, the core functions `0, …, n - 1` and
  the inline core instances (`Prefix`, `Root`, over `core3 o`); the module's imports resolve to
  the trampolines (`Core.coreImportsFor_low`); the IR's store of fresh imports renames to that
  store (`Sim.mapH_irStore`), and preparation and host-free runs commute with renaming host code
  (`Sim.prepareE_mapH`, `startTrap_low`): no relocation, so no split condition. Results:
  `firstImp_fail_ref` (a quiet failure traps; a quiet failure makes **no** import call, since a
  typed callout's `i32` argument lifts to `u32` and the wiring then calls `f`,
  `IR.nodeFailImp_cases`); `firstCore'_fail_ref` on `FirstCoreFrag' = FirstCoreFrag ∨
  FirstImpFrag`; with host calls (`NodeCalls`): each segment of the IR's start run is run in the
  machine, the core activation to the trampoline's callout, the `canon lower` callout program
  through the logging host (`Callout.hostCall_lrunX`, the `Reference.CalloutRun` path restated
  over any engine and function type) and the resumption, which is the IR's
  (`Start.startRun_ref`); so `firstImp_failCalls_ref` (a failure after host calls traps) and
  `firstImp_ready_ref` (a ready node: the machine reaches the start function's return with the
  host log `logOfCalls t`, or traps before the first core instantiation, or `t = []`). The
  remaining failure cases are `Task.failRefWiredRest'` (**open**: node `k ≥ 1`, or outside
  `FirstCoreFrag'`); `failRefWiredRest_of_rest'` proved.
* `DecoderBridge.Multi` (proofs in `Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi`;
  `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`): **the start goal on several core
  instantiations, reduced to the export call**. `Task.startAdequacyFrag` is `Task.startAdequacy`
  on the decidable fragment `MultiImpFrag` (`starts.wasm` is in it, `starts_multiImpFrag`,
  kernel). `startAdequacyFrag_of_nodes` derives it from (a) `Task.nodeCallsIR`, **proved**
  (`nodeCallsIR`: each round of a node's play is one call of `f`, `IR.startRun_calls`), the
  instantiation `Task.nodesRef`, **proved** (`nodesRef`), and (d) `Task.exportRef`, **open**;
  `startAdequacyFrag_of_d`, `starts_of_d`: the goal on the fragment, and the REF half of
  `starts.wasm` from the IR run, given (d). The proof of `Task.nodesRef`:
  * **the first node** (`firstK'`): the root checks pass on `rootShape`, with the continuation of
    the definitions tracked (`RootK.root_firstK`, `FocusAtK`) and shown to finish the
    instantiation (`KFin`: nesting back, the instantiation observed, the host back in control);
    the first core instantiation as in `firstNodeRef` (start call with its epilogue,
    `Start.start_atG`; the IR's start run in the machine, `Run.startRun_refX`), ending in the
    machine invariant `LaterInv` and the frame related to the symbolic reading (`FrameRel`);
  * **the store relation** (`Multi.GapShift`): a later node's IR store `t` (its `b` imports
    first) is mapped into the shared core store `pre` built by the earlier nodes as
    `Gap.rel ⟨pre, b⟩ t`: `pre`, then `t` without its imports, every address mapped
    (`GShift`: function addresses below `b` kept, the others moved past `pre`; the other
    address spaces shifted past `pre`), valid when the first `b` functions of `pre` are the
    trampolines (`Gap.PreOk`). Preparation commutes with it (`prepare?_gap`,
    `instantiateOnce?_gap`, `GapCore.prepareE_gap`), so do host-free Core steps of the split
    fragment (`GapStep.step_gap`, `steps_gap`, adapted from `Reference.ShiftStep`), callouts,
    returns and resumption (`GapRun`), and the IR's start run with its host calls in the machine
    (`GapMachine.startRun_gapX`);
  * **a later core instantiation** (`LaterCore.laterCoreStep'`): its imports resolve to the
    trampolines (`coreImportsFor_shared`), its preparation is the IR's mapped, its start function
    runs in the shared store with the host calls of the IR's node, the start epilogue returns,
    its core instance holds the module's exports (`prepareE?_exports`), and `LaterInv` holds
    again (the component instance's thread table after one start thread, `ι₁`);
  * **the other definitions** (`Nodes.nonCore_step`): types, core export aliases, lifts and
    exports run silently, keeping `LaterInv` and `FrameRel`; `later_run` walks the definitions
    after the first core instantiation, consuming the IR's later nodes in order, and finishes the
    instantiation with `KFin` (`nodesRef_of'`).
* `DecoderBridge.nodesInst_of_startPlay`: on an import-wired binary, the instantiation part of
  the IR play of `Task.startAdequacy` (`instPlay t .ready`, a prefix) is `NodesInst … t .ready`.
  The export call after `ready` is not decomposed (a node's export phase is reached through the
  routing layer from the right; not done).

What the rest needs: the remaining cases `Task.failRefWiredRest''` (a quiet failure of a node
`k ≥ 1` of a binary of `MultiImpFrag` is proved: the ready nodes before it run as in
`Task.nodesRef`, the failing node's preparation or start trap is mapped into the shared store,
`LaterFail.laterFail_ref`; `failRefWiredRest'_of_rest''`; the rest is open), other import shapes, modules with memories, tables or segments; for
`Task.startAdequacy` also the export phase on both sides (`Task.exportRef`: the IR's export call
decomposed down to the core run of the lifted function in its node's store, and the reference
session's call of the lifted function in the shared store, whose relation to that node's store is
the one `Gap.rel` gives after its instantiation; nothing after the last core instantiation
changes the core store); outside import-wired binaries, calls between core instances (one shared
REF store, direct calls; the IR routes them through the environment).

`DecoderBridge.Sem.Thms`: `starts_of : Task.startAdequacyChecked → <the REF half of starts_agree>` and
`trap_of : Task.failAdequacy → <the REF half of trap_agree>`: the examples are instances of the
general goals, their hypotheses discharged by the existing theorems (and `starts_inFrag`,
`starts_rootChecked`). On
these two binaries the conclusions are also proved outright, by execution (`starts_agree`,
`trap_agree`).

## Oracle: wasmtime (not a proof, not in CI)

`python3 -I tools/component-tests/oracle.py` writes `examples/component-tests/oracle.json`. The
wasmtime CLI cannot supply a host function for a component import (running a binary alone fails
with `component imports function f, but a matching implementation was not found`, recorded as
`alone`). The host is therefore a component, `tools/component-tests/host.wat` (`f(x)` sets
`trace := trace * 10 + x` and counts the calls), composed with the test binary by `wac compose`
(the test binary is embedded verbatim, recorded). `wasmtime run --invoke 'get()'` (then `trace()`,
`calls()`) instantiates the composition afresh each time.

| binary | observed | expected |
|---|---|---|
| `starts.wasm` | instantiates; trace `12` (`f(1)` then `f(2)`), 2 calls; `get()` = `42` | the same |
| `trap.wasm` | every invocation fails at instantiation: `wasm trap: wasm unreachable instruction executed` | whole-instantiation trap |

Provenance in the JSON: wasmtime 50.0.0 (SHA-256 `f95e5beb…00e9b7`), wac 0.12.0 (`7cd490ed…d3beda`),
wasm-tools 1.262.0 (`fe6a056d…18acb211`), the SHA-256 of each binary and composition, the commands
and their outputs.

## Explorer

The rows and shapes appear in the generic problem views. The view `#/component-tests`
(`tools/silmaril-project/src/project/explore/views/component-tests.js`) shows, per binary: the
bytes (download, SHA-256, WAT), imports, exports, core instances, the expected trace and outcome,
the rows with their status, the theorem strength, the reference-machine theorem, the oracle's
observations and verdict, and the assumptions and tool provenance. Data:
`examples/component-tests/{report,oracle}.json`, copied next to the page by `make pages`. Node test:
`tools/silmaril-project/tests/explore/component_tests_view.test.mjs`.

## Not covered

* General adequacy of `Comp.denI` with respect to the reference machine (only these examples;
  stated as `DecoderBridge.Task.failAdequacy` and `Task.startAdequacy`; on import-wired binaries
  the IR half of the failure goal is proved and its reference half `Task.failRefWired` is open
  outside the first-core cases: `Task.failRefWiredRest'`; `Task.startAdequacy` is false
  (`paramname.wasm`), its corrected form is `Task.startAdequacyChecked`; on the
  fragment `MultiImpFrag` the IR's node calls and the reference half of the first node with its
  start epilogue and the later nodes in the shared core store (the whole instantiation,
  `Task.nodesRef`) are proved, and the export phase is open: `Task.exportRef`).
* Divergence (not observed by the shapes).
* Other import types, several imports, nested components, resources, async.
* A relation between the two readings' wiring outside the fragment `InFrag`
  (`DecoderBridge.rel_of_decode` relates core instantiations for every binary;
  `relW_of_decode` relates wiring, imports and exports in the fragment); exported instances,
  on which the readings name different exports (`DecoderBridge.InstExport`); and a theorem
  relating `toRef` to the reference's own reading of `Binary.md`.
* That the reference machine's instantiation follows the symbolic reading `refRead` (a
  simulation between its frames and `refRead`), and every behavioural statement beyond the
  executed examples.
