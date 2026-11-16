# Wasm catalogue: models, verified artifacts, emulators, tools and bridges

This page lists the WebAssembly work in this repository by kind and links the entry point for
each. Two kinds are easy to confuse and are kept apart:

* **semantics and interpreters *of* Wasm** (section 1) define what a Wasm program does;
* **programs *written in* Wasm** (sections 2 and 3) are checkers, examples and emulators whose
  Wasm code is the object of the proofs.

**Verified source, verified bytes and tested binaries are different claims.** For each artifact
the tables say which one applies:

* **module** — theorems about a Lean `Module` value, quoted from WAT (`wat3!`) or built in Lean;
* **bytes** — the module is also tied to an exact byte string (`decode_bytes`, `encodeModule_eq`,
  a pinned SHA-256);
* **tested** — the artifact is exercised (difftests, interpreter runs, conformance suites), not
  proved.

Unless a row says otherwise, theorems hold at every numeric profile and host relation, and use
only `propext`, `Classical.choice` and `Quot.sound`.

## 1. Semantic models (shapes) and how they are related

The Core 3.0 small-step semantics (`Silmaril.Wasm.Execution.Core`) is the reference. The other
shapes are connected to it by proved relations, and are generic where possible
(`Silmaril.Games.Abstract`).

| Shape | Entry point | Relation to Core 3.0 (proved) | Scope and caveats |
| --- | --- | --- | --- |
| Small-step, behaviour sets (V1, V2, V3 = Core 3.0) | `Silmaril.Wasm.Behaviour.Semantics.{V1,V2,V3}` (`behavioursOf`, `behaviours`) | definition | [wasm-semantics.md](wasm-semantics.md) |
| Interpreter (native, fuel-based) | `Silmaril.Wasm.Binaryen.{run, invokeRun, nbeh}`; adequacy in `Silmaril.Wasm.Interp.Thms`; common case `Silmaril.Wasm.Interp.Closed` (`callOk`, `behaviours_eq`) | `native_adequacy`: `behaviours P closedHost s a vs = nbeh s a vs`; `native_store_adequacy` (final stores too) | needs a typed store (`StoreOk`), the native integer fragment (`NativeFuncsOk`, decided by `nativeFuncsB`), the arity check (`StoreChk`, decided by `storeChkB`) and a typed call (`InvokeOk`, decided by `invokeOk?`). No floats, packed or bulk memory, `memory.grow`, tables |
| Kernel evaluator | `Silmaril.Wasm.Verify.Kernel` (`runInvokeF_eq`) | runs of the verified interpreter are Core runs, by kernel evaluation | used by the LRAT and acceptor examples below |
| Denotational: abstract functions and modules | `Silmaril.Wasm.Abstract.Function` (`wasmFun`), `Silmaril.Wasm.Abstract.Module` (`wasmShape`, `wasmModule`), bodies `Silmaril.Wasm.Abstract.Body` (`BodyM`, `bodyM_lawfulElgot`) | `wasmFun` agrees with `behaviours` (`Abstract.Function.Thms`); closing a module is the closed semantics (`close_wasmOpen`, `wasmFun_eq_close`, `behaviours_eq_closed`) | host calls are resolved inside the store semantics in `wasmFun` (no import interface); the open forms use `Abstract.OpenStrat` |
| Denotational: components | `Silmaril.Wasm.Component.Semantics` (`Comp.den`, `Comp.denU`), concrete core semantics `core3Sem P` (`Component.Reference.Core3Sem`) | `denU_core3Sem_le`, `optimizeComponent_sound_core3`; IR against the reference machine `Simple.adequacy` (`Component.Reference.Adequacy`) | component adequacy covers `Simple` components only: [component-caveats.md](component-caveats.md) |
| Game semantics: strategies | `Silmaril.Wasm.Game` (`ScalarInstance.strategy`) | `adequacy_profile`, `adequacy_answers`, `adequacy_of_no_mixed` (`Wasm.Game.Adequacy.Thms`); with trace models `strategyIso_strategy`, `denote_detUpTo` (`Abstract.Instance.Thms`) | needs `I.WellFormed s`; the trace-model square is for scalar instances |
| Game semantics: sessions and canonical plays | `Silmaril.Wasm.Abstract.{InstSession, HostSessionXP, LinkCore, OpenStrat}`, `Silmaril.Games.Abstract.{StratSession, CanonStrat}` | linking with the host as a strategy is the closed Core semantics (`LinkCore`); native and Core sessions are equal (`HostSessionXP`) | [games.md](games.md), [component-semantics.md](component-semantics.md) |
| Entry-point refinement | `Silmaril.Wasm.Equiv.Module` (`ModuleRefines`, `ModuleEquiv`) | definition over `behaviours` | the optimizer contracts: [wasm.md](wasm.md) |

### Institutions over these shapes

`Silmaril.Wasm.Institution.Api` is the front door. Every Wasm institution comes from an
observational semantics (`Institution.Generic`, `ObsSemantics`) through the facade
`Silmaril.Inst` ([logic-inst.md](logic-inst.md)). Worked examples and the scope of core-module vs
component institutions: [wasm-institutions-guide.md](wasm-institutions-guide.md).

| Institution | Module | What its models are |
| --- | --- | --- |
| Entry points | `Wasm.Institution.Entry` | single invocations of exports in a fixed environment, the logic of `ModuleRefines` |
| Sessions | `Wasm.Institution.Session` (`valid_coreRef_iff`) | export calls sharing a store, the logic of `ExportRefines` |
| Reduction, LTS and games | `Wasm.Institution.{Graph, Games, GameGraph, DivGames}` (`behOf_wasmRed`) | the 12-node phase-1 graph, reduction → LTS → game with divergence |
| Components | `Wasm.Institution.{Components, CompGraph}` (`compGraph`, `fullGraph₂`, `valid_wrap_iff`, `valid_flatten_iff`) | components over any `CoreSem`, wrapping and flattening |
| Game instantiations | `Wasm.Institution.{GameInst, SpecGInst, GameReadings, WasmiGame, CompGameGraph}` | instances and readings of game semantics |
| Simulators | `Silmaril.Sim.Institution` ([wasm-sim.md](wasm-sim.md)) | ISA problems transferred along sound Wasm simulators |
| Consequence systems | `Silmaril.Wasi.Component.Consequence.Interp` (`coreInterp`, `coreBytesInterp`) | acceptor modules and components read as consequence systems ([consequence-systems.md](consequence-systems.md)) |

**Not connected yet:** `fullGraph₂` has no edge from the core-module institutions to the
component institutions instantiated at `core3Sem`, although both semantics exist.

## 2. Verified checkers and example programs in Wasm

| Artifact | Lean entry point | Claim | Main theorems |
| --- | --- | --- | --- |
| **LRAT proof checker** (streaming, RUP and RAT) | `Silmaril.Wasm.Examples.LRAT` (`lratModule`), component `LRAT.Component` | bytes: `examples/wasm-checkers/lrat.wasm`, 1812 B (`LRAT.Bytes.Thms`: `encodeModule_eq`, `decode_bytes`) | `lrat_session_unsat` (an `unsat` answer `1` in any session means the streamed CNF is unsatisfiable), `lrat_spec`, `lrat_init`; `unitPair_accepted`, `unitPair_session` (an accepted refutation, by kernel evaluation) |
| **Farkas certificate checker** | `Silmaril.Wasm.Examples.Farkas`, `Farkas.Component` | bytes: `examples/wasm-checkers/farkas.wasm`, 372 B (`Farkas.Bytes.Thms`) | `farkas_session`, `farkas_session_infeasible` (no solution over any ordered field) |
| **Member / empty checkers** | `Silmaril.Wasm.Examples.{MemberCheck, EmptyCheck}` | bytes (`examples/wasm-acceptors/`, registered in `silmaril/artifacts.toml`) | `encodeModule_eq`, `decode_bytes`, `check_verified`; `exportAccepted_eq` (MemberCheck), `exportAccepted_eq_empty` (EmptyCheck) |
| **JSON-subset acceptor** | `Silmaril.Wasm.Examples.JsonAccept` | bytes (`examples/wasm-acceptors/`) | `accept_verified`, `accept_sound_json` |
| Verified functions | `Silmaril.Wasm.Examples.Verified` | module; `double.wasm` bytes | `double_vc`, …, `double_verified` |
| Compiled adders (Rust, C, AssemblyScript) | `Silmaril.Wasm.Examples.{RustAdder, CAdder, AsAdder}` | bytes (`examples/wasm-demos/*/wasm/adder.wasm`, SHA-256 in the headers) | decode theorems plus call specifications |
| Rust institution examples | `Silmaril.Wasm.Examples.RustInst` | module (the WAT is the `wasm2lean` output; that it decodes the binary is trusted) | `adder_*`, `door_*` |
| Annotated WAT | `Silmaril.Wasm.Examples.{Wat, WatSpec, WatSpecSt}` | module | function specifications by `wat_vc` |
| **Specification library** | `Silmaril.WasmSpec.*` ([wasm-spec-library.md](wasm-spec-library.md)) | module (WAT checked against the quotation) | Adder, Add3, Abs, Max, SumTo, IsSorted, InsertionSort, MergeSort, BTree v1 (partial) and v2 |

## 3. Emulators written in Wasm

| Artifact | Entry point | Claim |
| --- | --- | --- |
| x86-64 run-time simulators `x86-g.wat`, `x86-m.wat` | `examples/wasm-sim/x86/`, quoted in `Silmaril.Sim.X86Real` | **tested** against the host CPU; the G accessors and `i_alu_rr` are proved on the quoted code |
| Certified G translator (x86-64 register fragment → Wasm methods) | `Silmaril.Sim.X86.{G, GModule, GCert, GInst, Loop}`, `Silmaril.Sim.SysV` | module: `emit_sound`, `GCert.sound`, `reduce_inst`; System V contracts of real code (`Sim.X86.Max`, `SumTo`) |
| Simulation framework | `Silmaril.Sim.{Core, Wasm, Reduce, Institution}` | proved transfer of angelic and demonic properties along simulations |

Details: [wasm-sim.md](wasm-sim.md), [wasm-sim-abi.md](wasm-sim-abi.md),
[wasm-sim-reduction.md](wasm-sim-reduction.md).

## 4. Tools

| Tool | What it does | Trust | Docs |
| --- | --- | --- | --- |
| `wasm-as`, `wasm-dis`, `wasm-opt`, `wasm-merge`, `wasm-shell`, `wasm-ctor-eval`, `wasm-metadce` (`sil wasm …`) | Binaryen-compatible tools in Lean | contracts proved for supported operations | [wasm.md](wasm.md), [wasm-tools-trust.md](wasm-tools-trust.md) |
| `wasm-check` | refutes or proves equivalence and refinement of two modules | verdicts come with kernel-checked certificates | [wasm-binaryen-tooling.md](wasm-binaryen-tooling.md) |
| `wasm-verify` | decodes a module and runs the verified checker `Silmaril.Wasm.Verify.check` | `check_sound`, `checkFrom_sound` | [wasm-extras.md](wasm-extras.md) |
| `wasm-tools`, `wasm-jco`, `wasm-wac`, `wasm-wit` | component and WIT tooling | see each page | [wasm-components.md](wasm-components.md) |
| `wasm-pages` | the explorer's Wasm pages (CFGs, component structure) | runtime; what each fact rests on is listed | `tools/wasm-pages/README.md` |
| `wasm-sim` (Rust) | generates, difftests and reduces the x86 simulators | untrusted | [wasm-sim.md](wasm-sim.md) |
| `wasm-vc` (Rust) | solves small Wasm problems (symbolic execution + SMT), generates `tactic+script` spec-library proofs and Lean statements | untrusted; Lean re-checks what it generates | [wasm-solvers.md](wasm-solvers.md) |

## 5. Bridges to other regions

* **Wasm ↔ SSA:** `Silmaril.Wasm.Abstract.SSAFragment` (`wasmFun_ssaFragment`), `Silmaril.Wasm.SSA`.
* **Wasm ↔ x86-64:** `Silmaril.Sim` (simulators in Wasm, section 3).
* **Wasm ↔ logic:** acceptors as consequence systems (`coreInterp`), and the LRAT and Farkas
  checkers as certificate checkers for SAT and linear arithmetic (section 2).
* **Wasm ↔ WASI and processes:** [wasm-wasi.md](wasm-wasi.md).
