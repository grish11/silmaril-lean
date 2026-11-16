# Reducing ISA problems to Wasm problems

Status: experimental. The Lean framework (simulators, certificates, transfer) is described in
[wasm-sim.md](wasm-sim.md); the simulator ABI in [wasm-sim-abi.md](wasm-sim-abi.md).

**In this repository:** the generic reduction (`Silmaril.Sim.Reduce.{Core,X86,Wasm,PCalls,Loop}`),
the `wasm-sim reduce` translator and DAG checker (`tools/wasm-sim`) and the split x86 problems
under `examples/wasm-sim/x86/problems`. **Not in this repository yet:** the end-to-end toy
(`examples/wasm-sim/reduce/toy`, `Silmaril.Sim.Reduce.Toy`: its committed `toy.elf` still needs a
reproducible build receipt), the problem-catalogue registrations (`Silmaril.Problems.WasmSim`,
`Problems.FnCorrectDet`) and the RV64 problem DAGs. Statements about them below are marked.

An x86-64 (later RISC-V, C, HOL) problem is **posed as one or many Wasm problems** about a
simulator, and Wasm solutions are transported back by proved theorems. This page states what
the pipeline produces, what is proved, and what is only tested or assumed.

## The pipeline

```
x86 problem                     reduce.toml (ELF, contracts, cut invariants, Lean names)
FnContract.Spec.Total I S  ──►  wasm-sim reduce (tools/wasm-sim)
FnCorrectDet I S                │
                                ├─ modules/<fn>.wat     P-calls translation, annotated
                                ├─ pieces/ag/<fn>/piece.json
                                ├─ dag.json             pieces + composition edges
                                └─ link/                mem, sys, nd, System V driver
                                wasm-sim reduce --run       (linked to the simulator, vs native)
```

1. **ISA problem.** A System V contract `FnContract.Spec.Total I S` on an x86-64 model
   (`Open9.isa`, the shape `silmaril.shapes.x86.contract.open9`), or the problem template
   `Silmaril.Problems.FnCorrectDet I S` (every placement). Generically: `IsaReach step Pre Post`
   for any machine with a partial step (`spec_total_iff` identifies the two).
2. **Wasm problem.** For a simulator `K` with a representation relation `R` between Wasm states
   and the ISA states they represent, `specWasm I S K Init`: from every freshly loaded
   simulator state (`Init`) representing a state that meets the contract's entry, the simulator
   can halt in a state all of whose represented states meet `Spec.Result` (the pre- and
   postcondition pulled back along `R`). For a certified Wasm simulator
   (`Silmaril.Sim.Wasm.ExportSim.Cert`, run-level `SoundSim.ofExportCert`) the same problem in the
   call-level form of the Wasm specification library is `Wasm.runSpec`: a `FuncSpec` of the
   simulator's export returning accepted results, the form `Silmaril.WasmSpec.*.CallSpec` entries
   state.
3. **Decomposition.** The emitter splits the Wasm problem into many small ones (below), each
   self-contained (WAT + statement + suggested solvers), with a composition theorem per edge.
4. **Transport back.** `specReduction` / `specRunReduction` (for `FnCorrectDet`, every
   placement: `Problems.WasmSim.fnCorrectDetReductionStmt_sol`, not in this repository yet).

## What is proved (Lean, standard axioms, audited by `#guard_msgs`)

`Silmaril.Sim.Reduce.Core` is ISA-agnostic; `Silmaril.Sim.Reduce.X86` holds the System V instance;
`Silmaril.Sim.Reduce.{Defs,Thms}` re-export both.

| theorem | statement |
|---|---|
| `isaReach_of_wasmTotal` | sound simulator + `Encodes` (every ISA entry state is represented by a loadable simulator state) ⇒ (Wasm problem ⇒ ISA problem) |
| `specReduction` | the same for `FnContract.Spec.Total` (the `Problems.FnCorrectDet` form is not in this repository yet) |
| `Wasm.wasmTotal_of_runSpec`, `Wasm.specRunReduction` | the call-level `FuncSpec` of a certified simulator's export (Core 3 small-step semantics, any profile/host) solves the run-level Wasm problem, hence the x86 contract |
| `wasmTotal_of_isaReach`, `reachExact`, `specExact` | completeness on the modelled fragment (`RunComplete`, also `Complete`) ⇒ exact reduction (silmaril `refutation_route`) |
| `isaCex_of_wasmCex`, `not_isaReach_of_isaCex` | a Wasm counterexample gives an ISA counterexample at a state it represents (given `Complete`) |
| `ag_compose`, `agDecomp` | per function: assume-guarantee pieces over an acyclic call graph compose |
| `cut_compose` | per cut point: block pieces with invariants and a measure compose (total correctness) |
| `SoundSim.ofSteps` | per method: per-instruction-form soundness pieces give a sound (decoding) simulator |
| `SoundSim.ofRefines`, `wasmTotal_of_refines` | simulator refinement (G ≡ M, lattice inclusions) transfers soundness and Wasm solutions |
| `SoundSim.ofSimulation`, `SoundSim.ofExportCert`, `wasmTotal_ofSimulation_iff` | the step-level interface (`Silmaril.Sim.Simulation` against `Machine.ofStep`; a certified `Silmaril.Sim.Wasm.ExportSim`) gives a `SoundSim`, and the Wasm problem is its angelic `loop` property |
| `Decomp.solve`, `Decomp.refine`, `Decomp.Exact.refute` | decompositions compose, refine piecewise, and transfer refutations when exact |

`Decomp` (`goal`, `pieces`, `compose`) is the one reduction record: a plain reduction is
`Decomp.single`, pieces refine (`Decomp.refine`), and `Decomp.Exact` gives refutation transfer.
They are the `decomposition` (`c₁ → … → p`) and `refutation_route` (`¬c → ¬p`) records of a
silmaril project DAG ([silmaril-projects.md](silmaril-projects.md)). The institution's goal-indexed
`Silmaril.Sim.Institution.Reduction` converts by `Decomp.ofReduction`/`toReduction`; the legacy
two-field `Reduction` (`src`, `tgt`, `sound`, used by `specReduction`) by `Reduction.toDecomp`.

## The simulator interface

`SoundSim σ W` is the run-level projection of a sound simulator: the reference `step`, the
halting runs `run`, the representation relation `R`, and **`sound`: every simulator run from a
state representing `s` is backed by a reference run from `s` to a state the final simulator
state represents**. This is the only fact about the simulator the reduction uses. Simulators
are certified at the step level (`Silmaril.Sim.Wasm.ExportSim.Cert`, a `Silmaril.Sim.Simulation`;
[wasm-sim.md](wasm-sim.md)) and projected by `SoundSim.ofExportCert` / `SoundSim.ofSimulation`; every
reduction theorem is stated for an arbitrary `K`. Side conditions per problem: `Encodes`
(loadability; for a G-state simulator: `set` every modelled location and supply memory through
the `mem` module) and, for refutations only, `RunComplete`.

`RunComplete` is a hypothesis, not a theorem: it holds for a deterministic reference machine
and a simulator that models every instruction and location the runs touch and halts exactly at
the first `Post` state (first return). A simulator returning status `2` (unsupported) or
touching an unmodelled location makes it false, and then a Wasm counterexample proves nothing.

## Decomposition: one problem → a DAG of small Wasm problems

`dag.json` (`silmaril.wasm-sim.dag.v0`) lists nodes (`isa-problem`, `wasm-problem`,
`wasm-piece`, `translation-validation`, `simulator-soundness`, `side-condition`) and edges
`goal ⇐ pieces` naming the composition theorem and its status (`proved` or `task`).

| piece | statement | solvers |
|---|---|---|
| `ag/<fn>` | `AGPiece`: `fn`'s Wasm problem assuming its callees' (callees are imports with `@assume` contracts, as `Silmaril.WasmSpec.Add3` assumes `Adder.CallSpec`) | `wpc`/`HWP`, `wasm-vc`, agents |
| `cut/<fn>/<addr>` | `CutPiece`: from a loop head with its invariant, reach the exit or a cut with smaller measure | VC + SMT per cut |
| `method/<m>` | `StepPiece`: the simulator method `m` refines the reference semantics of its forms | Wasm refinement (`Silmaril/Games`), `wpc`; difftest |
| `tv/<fn>` | the P-calls module performs the method calls of the decoded bytes | a decidable checker (to be verified) |
| `refine/G-M` | `SimRefines` between representations | Wasm equivalence; lockstep difftest |
| `sim/encodes/<fn>` | `Encodes` | Lean |

Edges: `isa/<fn> ⇐ wasm/<fn>, sim/sound, sim/encodes/<fn>` (`specReduction`, proved);
`wasm/<fn> ⇐ ag/<g>` for `g` in `fn`'s callee closure (`agDecomp`, proved);
`ag/<fn> ⇐ cut/<fn>/…` for functions with loops (`cut_compose`, proved);
`sim/sound ⇐ sim/sound[M], refine/G-M` (`SoundSim.ofRefines`, proved);
`sim/sound ⇐ method/…, tv/…` (**task**: P-calls soundness from method soundness and
translation validity is not yet a theorem; for a decoding simulator, `SoundSim.ofSteps` is).

## Running the translator

```sh
cargo build --release --locked --manifest-path tools/wasm-sim/Cargo.toml
tools/wasm-sim/target/release/wasm-sim reduce <reduce.toml> -o <out> [--run --native <exe>] [--granularity insn]
tools/wasm-sim/target/release/wasm-sim dag check <out>/dag.json
```

`reduce.toml` names an ELF, the System V contracts as SMT-LIB terms over simulator locations
(`(reg rdi)`, `(old …)`), loop invariants and the Lean names of the goal. The end-to-end toy
input of this page (`f(a, b) = sum_to(a) + dbl(b)`) is not in this repository yet (see above).

Tooling: one translator, the crate `tools/wasm-sim` (P-calls translation,
`x86::problem::split`), with `src/reduce/` (DAG schema and validator, plan schema,
per-instruction step methods `insn`, ELF reader) and `src/x86/reduce.rs` (the `reduce`
subcommand).

### DAG schema `silmaril.wasm-sim.dag.v0`

`{schema, id, title, root, artifact, isa, sim, lean, nodes, edges}`. A node: `id`, `kind`
(`isa-problem | wasm-problem | wasm-piece | translation-validation | simulator-soundness |
side-condition`), `status` (`open | solved | refuted | tested`), optional `statement`, `lean`,
`solution` (required when solved), `refutation`, `problem` (a `silmaril.problem.v1` ID), `files`,
`solvers`. An edge: `goal`, `pieces`, `theorem` (required when proved), `status` (`proved |
task | tested`; `open` accepted as `task`), `note`. Semantics: an edge `goal ⇐ pieces` with
status `proved` names a Lean theorem `pieces → goal` (a `Silmaril.Sim.Reduce.Decomp`); the
derived status of a node is solved if it is solved or some proved edge has all pieces derived
solved. `wasm-sim dag check` validates (ids, kinds, statuses, references, acyclicity) and
prints the derived status.

## What is trusted

* **Proved**: everything in the table above, for every sound simulator.
* **Proved end to end (in this repository)**: `Silmaril.Sim.X86.Max` and `SumTo` (System V
  contracts `FnContract Open9.isa` of assembled bytes on `Silmaril.X86.Ext`, through the certified
  G translator and the dispatcher); at the Wasm level, the P-calls `max` from its method
  specifications (`Silmaril.Sim.X86.Calls`) and the `max2` problem module
  (`Silmaril.Proofs.Sim.X86.Max2.Main`, `max2_valid`).
* **Assumed (open leaves)**: the method specifications for a concrete simulator (pieces
  `method/*`), simulator soundness (`sim/sound`; the run-time simulators are only difftested), `Encodes`, the cut pieces as separate problems, and the P-calls composition
  `task`.
* **Untrusted tooling**: `wasm-sim reduce` (ELF reader, iced-x86 decoder, translator,
  annotations). Its outputs carry no trust: the translation is checked by `tv/<fn>`, and the
  contracts in `reduce.toml` are a convenience view of the Lean `spec` (their agreement is not
  checked; the Lean statement is the problem).
* **Not covered**: recursion (the call graph must be acyclic; a measure-indexed `ag_compose`
  is the extension), indirect calls and tail calls (rejected), instruction forms outside the
  method API (translated to `unreachable` with a warning), demonic model classes
  (`FnCorrect (Class.below A)`): the reduction targets the deterministic singleton class.

## Toward C, HOL, ACL2: further comorphisms

The same three ingredients — a reference semantics, a Wasm program whose runs are backed by
it (`sound`), and a representation relation — make further edges into the Wasm node of the problem graph:

* **C.** Silmaril has a pinned Cerberus C semantics (`Silmaril/Cerberus`, `tools/csem`) and a native
  C compiler running in Lean (`ccomp`, [ccomp.md](ccomp.md)), but no C → Wasm path. Two routes: (a)
  compose existing C → x86 translation validation (`elf-tv`) with this reduction (C problem ⇒
  x86 problem ⇒ Wasm problem; `Decomp.refine`); (b) a Wasm simulator of the Cerberus Core
  transition system, with soundness against `Silmaril/Cerberus/Core`, so C problems become Wasm
  problems directly. (a) reuses everything here; (b) avoids compiler trust.
* **HOL / ACL2.** A proof kernel compiled to (or written in) Wasm is a simulator of the
  logic's derivability relation: `sound` says every accepted certificate is a derivation, and
  the representation relates the kernel's term store to the logic's sentences. A HOL problem `⊢ φ`
  then reduces to the Wasm problem "the kernel, run on some certificate, accepts `φ`", which a
  Wasm-level solver (or a certificate search) attacks. The HOL node already has an
  interpretation into extensional MLTT; the kernel-in-Wasm
  edge would be a second, executable route.

## Next steps

* Project `Silmaril.Sim.X86.GCert.cert` through `SoundSim.ofExportCert` into a `sim/sound`
  node; discharge `Encodes` for G-state.
* Prove the method specifications for a concrete simulator module (the `method/*` pieces).
* Prove the P-calls composition for the method-relative route (methods + translation
  validity ⇒ simulator soundness). With
  split methods (`i_mov_rr` then `i_next`) the intermediate states are not ISA states, so the
  natural route is per-instruction methods (`Silmaril.Sim.X86.G.emit i len`) or a ghost "pending
  instruction" in the representation.
* Generate the WasmSpec entries of the AG pieces from `reduce.toml` (today hand-written from
  the emitted WAT).
* Register the DAG as silmaril records once the statements are closed (concrete simulator).
* RISC-V: the same reduction with `step` = the RV64 step (no change to the generic layer).
