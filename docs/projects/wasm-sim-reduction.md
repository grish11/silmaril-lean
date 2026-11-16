# Reducing ISA problems to Wasm problems

Status: experimental. The Lean framework (simulators, certificates, transfer) is described in
[wasm-sim.md](wasm-sim.md); the simulator ABI in [wasm-sim-abi.md](wasm-sim-abi.md).

**Not in this repository yet:** the problem-catalogue registrations (`Problems.WasmSim`). They
state the toy's problems with `Silmaril.Problems.FnCorrectDet`, which is over
`Silmaril.X86.FnContract`, while this development uses the parallel copy
`Silmaril.Machine.X86.FnContract`; the two copies must be unified first. The RV64 problem DAGs
are not here either (the RV64 simulators are not). Statements about them below are marked.

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
| `Toy.isa_of_pieces` | the toy: three per-function Wasm pieces ⇒ the three `FnCorrectDet Open9.isa` problems |
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
`docs/projects/wasm-sim.md`) and projected by `SoundSim.ofExportCert` / `SoundSim.ofSimulation`; every
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

## The toy (end to end)

`examples/wasm-sim/reduce/toy`: `f(a, b) = sum_to(a) + dbl(b)` (`toy.S`; `sum_to` has a loop,
`f` saves `rbx`/`r12` and calls both). `reduce.toml` gives the contracts as SMT-LIB terms over
simulator locations (`(reg rdi)`, `(old …)`), one loop invariant and the Lean names of
`Silmaril.Sim.Reduce.Toy` (`isaGoal`, `J`, `piece`, `isa_of_pieces`).

```sh
examples/wasm-sim/reduce/toy/build.sh                     # toy.elf (committed) and build/toy-native
cargo build --release --manifest-path tools/wasm-sim/Cargo.toml
wasm-sim reduce examples/wasm-sim/reduce/toy/reduce.toml -o examples/wasm-sim/reduce/toy/out \
  --run --native examples/wasm-sim/reduce/toy/build/toy-native [--granularity insn]
wasm-sim dag check examples/wasm-sim/reduce/*/out/dag.json
```

Tooling: one translator, the crate `tools/wasm-sim` (P-calls translation,
`x86::problem::split`), with `src/reduce/` (DAG schema and validator, plan schema,
per-instruction step methods `insn`, ELF reader) and `src/x86/reduce.rs` (the `reduce`
subcommand).

### DAG schema `silmaril.wasm-sim.dag.v0`

`{schema, id, title, root, artifact, isa, sim, lean, nodes, edges}`. A node: `id`, `kind`
(`isa-problem | wasm-problem | wasm-piece | translation-validation | simulator-soundness |
side-condition`), `status` (`open | solved | refuted | tested`), optional `statement`, `lean`,
`solution` (required when solved), `refutation`, `problem` (a problem ID), `files`,
`solvers`. An edge: `goal`, `pieces`, `theorem` (required when proved), `status` (`proved |
task | tested`; `open` accepted as `task`), `note`. Semantics: an edge `goal ⇐ pieces` with
status `proved` names a Lean theorem `pieces → goal` (a `Silmaril.Sim.Reduce.Decomp`); the
derived status of a node is solved if it is solved or some proved edge has all pieces derived
solved. `wasm-sim dag check` validates (ids, kinds, statuses, references, acyclicity) and
prints the derived status;

Result (toy, `examples/wasm-sim/reduce/toy/out/dag.json`): 3 functions → 44 nodes (5 ISA
problems, 3 Wasm problems, 25 Wasm pieces, 4 translation-validation pieces, 5 side conditions,
2 simulator-soundness nodes), 30 leaves (independent problems: 21 Wasm pieces, 4
translation-validation pieces, 4 side conditions, 1 alternative soundness), 18 edges (13 proved,
5 task: the P-calls soundness edges of the method-relative route and `task/f`); 6 nodes solved
directly, and `isa/dbl`, `isa/sum_to` derived solved. `--run` with the run-time simulator
(state representations G and M) agrees with native execution on all 4 test vectors, including
the driver's System V return checks (`rip` = sentinel, `rsp` popped, `rbx rbp r12–r15`
preserved); the run-time simulator is tested, not proved.

### In the problem catalogue

Not in this repository yet (see the status note at the top): the `@[problem]` registrations of the
transfer principles and the toy's Wasm pieces wait for the unification of the two
`FnContract` copies.

## End to end: the toy's `dbl` solved through Wasm (P-calls soundness)

`Silmaril.Sim.Reduce.Toy.Dbl.isa_dbl : Toy.isaGoal .dbl` — the System V contract of `dbl`
(`mov %rdi,%rax; add %rax,%rax; ret`) on `Open9.isa`, at every placement of the toy's code —
is **proved from a solved Wasm piece** (standard axioms only):

1. `wasm-sim reduce --granularity insn` emits `insn/dbl.wat`: the 23 location globals, one
   **full step method per instruction** (WAT equal, by `rfl`, to the certified
   `Silmaril.Sim.X86.G.emit i len`; difftested against the P-mem simulator on 200 random states)
   and the P-calls body `dbl_body` = `call s_mov_rax_rdi_3; call s_add_rax_rax_3`. With
   per-instruction methods every state between calls is an x86 state.
2. Piece `wasm-insn/dbl` (`PieceStmt`, a `Silmaril.Sim.Reduce.PCalls.Piece`): every run of the body,
   the methods given only by their every-run step contracts, ends with `rax = rdi + rdi` and the
   other registers unchanged. Solved by the every-run call rule `hwp_call_step` (`piece`).
3. Method pieces and translation validity (`dbl_fns`): the instantiated module's calls reach
   functions whose code is `emit i len` (`rfl`, `decide +kernel`); `step_valid`
   (`Silmaril.Sim.X86.GCert`) gives their contracts.
4. **P-calls soundness** `Silmaril.Sim.Reduce.PCalls.xproblem_of_piece`: piece + concrete instance ⇒
   `XProblem` (the x86 problem on `Ext.exec`). The proof joins the every-run piece with the run
   that the certified methods' existential specs provide (`calls_wp`); no determinism argument.
5. `isa_of_x86`: decoding the bytes (`decide`), the final `ret`, and the contract on the open
   machine (`FnContract.total_of_ext_returns`, `Spec.Total.toOpen9`).

DAG (`examples/wasm-sim/reduce/toy/out/dag.json`): `isa/dbl ⇐ x86/dbl` (`isa_of_x86`),
`x86/dbl ⇐ wasm-insn/dbl, tv-insn/dbl, method/s_*` (`x86_of_piece`), all proved, all pieces
solved; `wasm-sim dag check` reports `isa/dbl` solved. (The catalogue registration of these two
pieces is not in this repository yet.)

**`sum_to` (a loop)** is solved too (`Silmaril.Sim.Reduce.Toy.SumTo.isa_sumTo`), through the x86
dispatcher route (`Silmaril.Sim.X86.Loop`) (P-inline with control flow, certified `emitX` methods with jumps, cut-point
rule `dispatch_hwp`): `isa/sum_to ⇐ x86/sum_to, term/sum_to` (`isa_of`), `x86/sum_to ⇐
wasm-disp/sum_to` (`xlproblem_of_lproblem`), `term/sum_to ⇐ wasm-rank/sum_to` (`term_of_rank`). The
functional piece is partial correctness; termination and frame come from a second **Wasm
piece**, a ranking of the dispatcher's entries (`Silmaril.Sim.Reduce.Loop.Ranked`: each entry's
code, evaluated by `exec`, lowers the rank), through the generic theorem
`Silmaril.Sim.Reduce.Loop.xrun_of_ranked` (with per-instruction-form lemmas for frame
`frame_of_exec`, progress `emitX_progress`/`progress_nf`, flags `flags_out`, successors
`rip_succ`). Flag definedness is a **decidable dataflow check** `flagsOK rt ann entry` over the
table at relative offsets with a certificate `ann` (offsets where the flags are defined; for
`sum_to` `[2, 5, 7, 10, 13]`, checked by `decide`), proved sound once. No per-function x86
reasoning remains: the rest is decoding by `decide` and the generic `ret`/ABI glue. The toy's
`sum_to` is the run-time test function (`xor/test/je/add/dec/jne`), as in `Silmaril.Sim.X86.SumTo`.

**`f` (the caller), by per-function decomposition** (`Silmaril.Sim.Reduce.Toy.F.isa_f`): `f`'s
dispatcher table holds only `f`'s instructions, so each `call` leaves it; `f` becomes three
**Wasm pieces** (`EntriesA/B/C`: the segments entry→`call sum_to`, return→`call dbl`,
return→`ret`, each a cut-point statement with a measure over the GM memory methods
`emitM`), and the callees enter only through their **solved ISA contracts** (`isa_sumTo`,
`isa_dbl`). `isa_f_of : EntriesA → EntriesB → EntriesC → isaGoal .sumTo → isaGoal .dbl →
isaGoal .f` is the assume-guarantee composition (AbiEntry from the pushed return address,
code outside the stack window, memory unchanged across callees). DAG: `isa/f ⇐ wasm-seg-a/f,
wasm-seg-b/f, wasm-seg-c/f, isa/sum_to, isa/dbl`; `wasm-sim dag check`: **root `isa/f`
solved, 3 of 3 toy goals**.

Compared with the monolithic `Silmaril.Sim.X86.Toy` `toyContract` (one dispatcher over all three functions,
28 cut points): the decomposed proof has 16 cut points for `f` and reuses the callees'
contracts unchanged; check time 12.2 s vs 20.7 s (`lake env lean`, 2 threads, one shared
machine: `Toy/F.lean` vs `Toy/{Main,X86,Contract}.lean`); 891 lines, of which ~250 are
generic glue proved once (`LProblemMB`/`reduce_loopMB` with final window bytes,
`progressM_nf`, window/load preservation, `tabAt_of_loaded`, `segment`), vs 731 (plus the
shared step lemmas). The callee proofs are independent pieces: changing `sum_to`'s code
re-proves only `isa/sum_to`. (The two proofs are on different `sum_to` codes: `Silmaril.Sim.X86.Toy`
keeps the earlier `mov/sub/jmp` loop.)

## What is trusted

* **Proved**: everything in the table above, for every sound simulator.
* **Proved end to end**: the toy's `dbl` (P-calls, per-instruction methods) and `sum_to`
  (dispatcher; with an x86-side termination/frame lemma) ISA goals on `Open9.isa`.
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

* Project `Silmaril.Sim.X86.GCert.cert` through `SoundSim.ofExportCert` into the toy's `sim/sound`
  node; discharge `Encodes` for G-state.
* Prove the method specifications for a concrete simulator module (the `method/*` pieces).
* Prove the P-calls composition for the method-relative route (methods + translation
  validity ⇒ simulator soundness). With
  split methods (`i_mov_rr` then `i_next`) the intermediate states are not ISA states, so the
  natural route is per-instruction methods (`Silmaril.Sim.X86.G.emit i len`) or a ghost "pending
  instruction" in the representation.
* Generate the WasmSpec entries of the AG pieces from `reduce.toml` (today hand-written from
  the emitted WAT; `scripts/check-wasm-sim.py` keeps the quoted ones identical).
* Register the DAG as silmaril records once the statements are closed (concrete simulator).
* RISC-V: the same reduction with `step` = the RV64 step (no change to the generic layer); the RV64
  simulators are not in this repository yet.
