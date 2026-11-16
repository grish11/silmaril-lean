module

public import Silmaril.Problems.Core.Defs
public import Silmaril.Sim.Reduce.Defs
public import Silmaril.Sim.Reduce.Toy.Defs
public import Silmaril.Sim.Reduce.Toy.Dbl.Defs

/-!
# Problems: the reduction of ISA problems to Wasm problems

The reduction of `docs/projects/wasm-sim-reduction.md` in the problem catalogue (`@[problem]` IDs
`wasm-sim/…`): its transfer principles as `pure-spec` problems, and the toy's ISA
problems and Wasm pieces.

**Transfer principles** (solved in `Silmaril.Proofs.Problems.WasmSim.Solve`):

* `wasm-sim/reduce/spec-reduction` (`specReductionStmt`): a solution of the Wasm problem
  `specWasm I S K Init` of a sound simulator `K` of `I` that can be loaded with every entry state
  solves the System V contract `S.Total I`;
* `wasm-sim/reduce/fncorrectdet-reduction` (`fnCorrectDetReductionStmt`): the same for the
  template `FnCorrectDet` (every placement);
* `wasm-sim/reduce/cex-transfer` (`cexTransferStmt`): on the modelled fragment
  (`Complete`), a Wasm counterexample is an ISA counterexample;
* `wasm-sim/reduce/ag-compose` (`agComposeStmt`): per-function assume-guarantee pieces
  over an acyclic call graph compose.

**The toy** (`examples/wasm-sim/reduce/toy`): the ISA statements `isaF`, `isaSumTo`, `isaDbl`
(`FnCorrectDet Open9.isa (Toy.spec g)`). Per-instruction route (`Silmaril.Sim.Reduce.Toy.Dbl`):
`wasm-sim/toy/insn/dbl-piece` (the P-calls piece) and `…/dbl-isa-of-piece` (piece ⇒ ISA
goal); both solved, so `isaDbl` is solved (`Silmaril.Sim.Reduce.Toy.Dbl.isa_dbl`). The ISA statements are not registered yet: a
`function` problem needs an artifact record and a nonvacuity companion (`problems-format.md`
§5).
-/

@[expose] public section

namespace Silmaril.Problems.WasmSim

open Silmaril.Sim.Reduce
open Silmaril.X86.FnContract (Spec)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86 (Open9.isa)

/-! ## Transfer principles -/

/-- **The x86 contract reduction**, as a problem statement. -/
@[problem "wasm-sim/reduce/spec-reduction"]
def specReductionStmt : Prop :=
  ∀ (τ W : Type) (I : Isa τ) (S : Spec τ) (K : SoundSim τ W) (Init : W → Prop),
    K.step = I.step → Encodes K Init (specPre I S) → specWasm I S K Init → S.Total I

/-- **The `FnCorrectDet` reduction**, as a problem statement. -/
@[problem "wasm-sim/reduce/fncorrectdet-reduction"]
def fnCorrectDetReductionStmt : Prop :=
  ∀ (τ W : Type) (I : Isa τ) (S : Silmaril.X86.Word → Spec τ) (K : SoundSim τ W)
    (Init : W → Prop), K.step = I.step → (∀ e, Encodes K Init (specPre I (S e))) →
    (∀ e, specWasm I (S e) K Init) → FnCorrectDet I S

/-- **Counterexample transfer**, as a problem statement. -/
@[problem "wasm-sim/reduce/cex-transfer"]
def cexTransferStmt : Prop :=
  ∀ (σ W : Type) (K : SoundSim σ W) (Init : W → Prop) (Pre : σ → Prop) (Post : σ → σ → Prop)
    (w : W), Complete K Init Pre Post → WasmCex K Init (pullPre K Pre) (pullPost K Post) w →
    ∃ s, K.R w s ∧ IsaCex K.step Pre Post s

/-- **Assume-guarantee composition**, as a problem statement. -/
@[problem "wasm-sim/reduce/ag-compose"]
def agComposeStmt : Prop :=
  ∀ (ι : Type) (J : ι → Prop) (callees : ι → List ι) (rank : ι → Nat),
    Ranked callees rank → (∀ i, AGPiece J callees i) → ∀ i, J i

/-! ## The toy -/

/-- The ISA problem of the toy's `f`. -/
def isaF : Prop := FnCorrectDet Open9.isa (Toy.spec .f)

/-- The ISA problem of the toy's `sum_to`. -/
def isaSumTo : Prop := FnCorrectDet Open9.isa (Toy.spec .sumTo)

/-- The ISA problem of the toy's `dbl`. -/
def isaDbl : Prop := FnCorrectDet Open9.isa (Toy.spec .dbl)

/-- The per-instruction P-calls piece of the toy's `dbl` (`Silmaril.Sim.Reduce.Toy.Dbl`). -/
@[problem "wasm-sim/toy/insn/dbl-piece"]
def dblPiece : Prop := Silmaril.Sim.Reduce.Toy.Dbl.PieceStmt

/-- **The reduction of the toy's `dbl`**: its Wasm piece solves its ISA goal (the System V
contract on `Open9.isa` at every placement), by P-calls soundness. -/
@[problem "wasm-sim/toy/insn/dbl-isa-of-piece"]
def dblIsaOfPiece : Prop :=
  Silmaril.Sim.Reduce.Toy.Dbl.PieceStmt → Silmaril.Sim.Reduce.Toy.isaGoal .dbl

end Silmaril.Problems.WasmSim
