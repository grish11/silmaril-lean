module

public import Silmaril.Machine.Execution
public import Silmaril.Sim.Institution.Defs

/-!
# Reducing ISA problems to Wasm problems: the ISA-agnostic core (definitions)

The problem-level side of simulators written in Wasm (`docs/projects/wasm-sim-reduction.md`). An ISA
problem (reachability of a machine with a partial step; on x86-64 a System V contract, in
`Silmaril.Sim.Reduce.X86`) is **posed as a Wasm problem** about a simulator, and the Wasm solution
is transported back. Nothing here mentions a particular ISA.

**The reduction record** (canonical):

* `Decomp`: a goal, a list of pieces and a composition theorem `(∀ p ∈ pieces, p) → goal`.
  Every reduction and decomposition is a `Decomp`; the pieces are what individual solvers or
  agents attack in parallel. `Decomp.single goal piece h` is a one-piece reduction.
* `Decomp.Exact`: the pieces also follow from the goal, so refuting a piece refutes the goal
  (`Decomp.Exact.refute`, in `Thms`).
* Derived views: `Silmaril.Sim.Institution.Reduction goal` is the same data indexed by the goal
  (`Decomp.ofReduction`, `Decomp.toReduction`, round trips by `rfl`), so the institution's
  combinators (`Reduction.trans`, `transfer`, `link`, `perCmd`, `chain`, `equiv`,
  `ExportSim.reduction`) produce `Decomp`s. `Reduction` (`src`, `tgt`, `sound`) is the legacy
  two-field form, kept because existing statements use it; new code uses `Decomp.single`.

**The run-level simulator interface**:

* `SoundSim σ W`: the run-level projection of a sound simulator. `σ` is the ISA state, `W` the
  Wasm-side state (a store); `run w w'`: running the simulator from `w` can halt in `w'`; `R`
  relates simulator states to the ISA states they represent; `sound`: each simulator run is
  backed by a run of the reference machine `step`. It is built from the step-level interface
  (`Silmaril.Sim.Simulation`, `Silmaril.Sim.Wasm.ExportSim.Cert`) by `SoundSim.ofSimulation` and
  `SoundSim.ofExportCert` (in `Thms`); its definition is frozen because registered problem
  statements mention it.
* `IsaReach step Pre Post`: total correctness (some run) of a machine with a partial step.
* `WasmTotal K Init Pre Post`: the Wasm problem: from every freshly loaded simulator state
  meeting `Pre`, the simulator can halt in a state meeting `Post`. `Pre` and `Post` are ISA
  predicates **pulled back along `R`** (`pullPre`, `pullPost`).
* `Encodes K Init Pre`: every ISA state meeting `Pre` is represented by a freshly loaded
  simulator state.
* `RunComplete K Init Pre Post` (also `Complete`): on the modelled fragment, every ISA run to a
  `Post` state is matched by a simulator run (needed only for refutation transfer).
* `WasmCex`, `IsaCex`: counterexamples on either side.

**Decomposition shapes**:

* `AGPiece`: per function, assume-guarantee: function `i`'s judgement assuming its callees';
  `ag_compose` and `agDecomp` (in `Thms`) assemble an acyclic call graph (`Ranked`).
* `CutPiece`: per cut point (loop head), a block-level problem with an invariant and a measure;
  `cut_compose` assembles them into reachability of the exit.
* `StepPiece`: per simulator method (instruction form): one step of that form is backed by the
  reference machine; `SoundSim.ofSteps` builds a sound simulator from them.
* `SimRefines`: a simulator refines another (a representation equivalence, or an inclusion in
  the lattice of partial simulators); `SoundSim.ofRefines` transfers soundness.
-/

@[expose] public section

namespace Silmaril.Sim.Reduce

open Silmaril.Machine.Execution (Reaches)

/-! ## The reduction record -/

/-- **A decomposition** (the canonical reduction record): a goal, its pieces, and the
composition theorem. A one-piece decomposition (`Decomp.single`) is a plain reduction. -/
structure Decomp where
  /-- The problem being decomposed. -/
  goal : Prop
  /-- The pieces, each a self-contained problem. -/
  pieces : List Prop
  /-- Solutions of all pieces assemble into a solution of the goal. -/
  compose : (∀ p ∈ pieces, p) → goal

/-- **An exact decomposition**: every piece follows from the goal, so a refutation of a piece
refutes the goal (a `refutation_route`). -/
def Decomp.Exact (D : Decomp) : Prop := D.goal → ∀ p ∈ D.pieces, p

/-- **A one-piece reduction**: solving `piece` solves `goal`. -/
def Decomp.single (goal piece : Prop) (h : piece → goal) : Decomp where
  goal := goal
  pieces := [piece]
  compose hp := h (hp _ (List.mem_singleton_self _))

/-- A goal-indexed reduction of the institution of simulators (`Silmaril.Sim.Institution`) as a
`Decomp`. -/
def Decomp.ofReduction {g : Prop} (r : Silmaril.Sim.Institution.Reduction g) : Decomp :=
  ⟨g, r.subgoals, r.sound⟩

/-- A `Decomp` as a goal-indexed reduction of its goal (the derived view). -/
def Decomp.toReduction (d : Decomp) : Silmaril.Sim.Institution.Reduction d.goal :=
  ⟨d.pieces, d.compose⟩

@[deprecated Decomp.ofReduction (since := "2026-11-10")]
alias Decomp.ofCore := Decomp.ofReduction

@[deprecated Decomp.toReduction (since := "2026-11-10")]
alias Decomp.toCore := Decomp.toReduction

/-- **A problem reduction, legacy two-field form**: solving the target problem `tgt` (a Wasm
problem) solves the source problem `src` (an ISA problem). Superseded by `Decomp.single`
(`Reduction.toDecomp`); kept because existing reductions (`specReduction`, `reachReduction`
and their users) are stated with it. -/
structure Reduction where
  /-- The source (ISA) problem. -/
  src : Prop
  /-- The target (Wasm) problem. -/
  tgt : Prop
  /-- Soundness: a target solution is a source solution. -/
  sound : tgt → src

/-- **An exact reduction**, legacy form of `Decomp.Exact`: also complete, so target
refutations are source refutations. -/
structure Reduction.Exact extends Reduction where
  /-- Completeness: a source solution gives a target solution. -/
  complete : src → tgt

/-- A legacy reduction as the canonical one-piece `Decomp`. -/
def Reduction.toDecomp (R : Reduction) : Decomp := Decomp.single R.src R.tgt R.sound

/-! ## The run-level simulator interface -/

/-- **A sound simulator, run-level**: the reference machine's partial step `step` on ISA states
`σ`, the simulator's halting runs `run` on Wasm-side states `W`, the representation relation
`R` (`R w s`: the simulator state `w` represents the ISA state `s` on what it models; for a
partial simulator one `w` represents many `s`), and soundness: a simulator run from a state
representing `s` is backed by a run of the reference machine from `s` to a state the final
simulator state represents. The run-level projection of `Silmaril.Sim.Simulation` against
`Machine.ofStep` (`SoundSim.ofSimulation`) and of `Silmaril.Sim.Wasm.ExportSim.Cert`
(`SoundSim.ofExportCert`). -/
structure SoundSim (σ W : Type) where
  /-- The reference machine (e.g. `Open9.isa.step`). -/
  step : σ → Option σ
  /-- Running the simulator from `w` can halt in `w'` (status `1`). -/
  run : W → W → Prop
  /-- The representation relation. -/
  R : W → σ → Prop
  /-- Soundness. -/
  sound : ∀ w w' s, R w s → run w w' → ∃ s', Reaches step s s' ∧ R w' s'

variable {σ W : Type}

/-- Total correctness (some run) of a machine with a partial step: from every state meeting
`Pre`, the machine reaches a state meeting `Post`. -/
def IsaReach (step : σ → Option σ) (Pre : σ → Prop) (Post : σ → σ → Prop) : Prop :=
  ∀ s, Pre s → ∃ t, Reaches step s t ∧ Post s t

/-- The precondition pulled back along the representation: `w` represents a state meeting
`Pre`. -/
def pullPre (K : SoundSim σ W) (Pre : σ → Prop) : W → Prop := fun w => ∃ s, K.R w s ∧ Pre s

/-- The postcondition pulled back along the representation: every pair of states that `w` and
`w'` represent meets `Post` (for a functional representation, `Post (abs w) (abs w')`). -/
def pullPost (K : SoundSim σ W) (Post : σ → σ → Prop) : W → W → Prop :=
  fun w w' => ∀ s s', K.R w s → K.R w' s' → Post s s'

/-- **The Wasm problem**: from every freshly loaded simulator state (`Init`) meeting `Pre`, the
simulator can halt in a state meeting `Post`. -/
def WasmTotal (K : SoundSim σ W) (Init : W → Prop) (Pre : W → Prop) (Post : W → W → Prop) : Prop :=
  ∀ w, Init w → Pre w → ∃ w', K.run w w' ∧ Post w w'

/-- Every ISA state meeting `Pre` is represented by a freshly loaded simulator state. -/
def Encodes (K : SoundSim σ W) (Init : W → Prop) (Pre : σ → Prop) : Prop :=
  ∀ s, Pre s → ∃ w, Init w ∧ K.R w s

/-- **Completeness on the modelled fragment**: from a freshly loaded state representing a
`Pre`-state `s`, every reference run from `s` to a `Post` state is matched by a simulator run
ending in a state meeting the pulled-back postcondition. It holds, for example, for a
deterministic reference machine and a simulator that models every instruction and location the
runs touch, represents states functionally, and halts exactly at the first `Post` state (first
return). Needed only for refutation transfer. The preferred name is `RunComplete` (distinct
from the step-level `Silmaril.Sim.Complete`); this one is kept as the definition because registered
problem statements mention it. -/
def Complete (K : SoundSim σ W) (Init : W → Prop) (Pre : σ → Prop) (Post : σ → σ → Prop) : Prop :=
  ∀ w s t, Init w → K.R w s → Pre s → Reaches K.step s t → Post s t →
    ∃ w', K.run w w' ∧ pullPost K Post w w'

/-- Run-level completeness on the modelled fragment (`Complete`), under the name that does not
clash with the step-level `Silmaril.Sim.Complete`. -/
abbrev RunComplete (K : SoundSim σ W) (Init : W → Prop) (Pre : σ → Prop) (Post : σ → σ → Prop) :
    Prop :=
  Complete K Init Pre Post

/-- A **Wasm counterexample**: a freshly loaded simulator state meeting the precondition from
which no halting run meets the postcondition. -/
def WasmCex (K : SoundSim σ W) (Init : W → Prop) (Pre : W → Prop) (Post : W → W → Prop) (w : W) :
    Prop :=
  Init w ∧ Pre w ∧ ∀ w', K.run w w' → ¬ Post w w'

/-- An **ISA counterexample**: a state meeting the precondition from which no run reaches a
state meeting the postcondition. -/
def IsaCex (step : σ → Option σ) (Pre : σ → Prop) (Post : σ → σ → Prop) (s : σ) : Prop :=
  Pre s ∧ ∀ t, Reaches step s t → ¬ Post s t

/-! ## Decomposition shapes -/

/-- **Per function (assume-guarantee)**: function `i`'s judgement, assuming those of its
callees. For a P-calls translation the judgements are `FuncSpec`s and the callees are imports
(as `Silmaril.WasmSpec.Add3.Spec` assumes `Adder.CallSpec`). -/
def AGPiece {ι : Type} (J : ι → Prop) (callees : ι → List ι) (i : ι) : Prop :=
  (∀ j ∈ callees i, J j) → J i

/-- An acyclic call graph: callees have smaller rank. -/
def Ranked {ι : Type} (callees : ι → List ι) (rank : ι → Nat) : Prop :=
  ∀ i, ∀ j ∈ callees i, rank j < rank i

/-- **Per cut point**: from a state at cut `c` meeting its invariant, the relation `R` (the
simulator's step, or a block of the program) reaches either a state meeting the goal `Q`, or a
state at some cut `c'` meeting its invariant with a smaller measure. -/
def CutPiece {ι : Type} (R : W → W → Prop) (Inv : ι → W → Prop) (μ : W → Nat) (Q : W → Prop)
    (c : ι) : Prop :=
  ∀ w, Inv c w → ∃ w', Relation.ReflTransGen R w w' ∧
    (Q w' ∨ ∃ c', Inv c' w' ∧ μ w' < μ w)

/-- **Per simulator method**: one simulator step of form `k` is backed by a run of the reference
machine (`method ⊑ reference`). -/
def StepPiece {κ : Type} (step : σ → Option σ) (R : W → σ → Prop) (form : κ → W → W → Prop)
    (k : κ) : Prop :=
  ∀ w w' s, R w s → form k w w' → ∃ s', Reaches step s s' ∧ R w' s'

/-- **Simulator refinement**: `h` maps states of the simulator `K₁` to those of `K₂`, runs to
runs, and preserves what they represent (a representation map such as globals ↔ memory, or an
inclusion in the lattice). -/
structure SimRefines (K₁ : SoundSim σ W) {V : Type} (K₂ : SoundSim σ V) (h : W → V) : Prop where
  run : ∀ w w', K₁.run w w' → K₂.run (h w) (h w')
  rel : ∀ w s, K₂.R (h w) s ↔ K₁.R w s

end Silmaril.Sim.Reduce
