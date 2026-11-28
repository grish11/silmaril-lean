module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Readback.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Readback.Correctness
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Thms

/-! # Exact operand round trip and complete packet validation -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Readback

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Edge)
open Silmaril.MLIR.Pure (Operands)
open Diamond.MLIR.CF (Label Widths)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {p : Program src entry}

/-- In this admitted profile, the two outer occurrences have different
source blocks, including when outer false is the header's direct edge. -/
theorem predecessor_key_injective (p : Program src entry) :
    Function.Injective (fun taken => (p.outerEdgeOccurrence taken).1) := by
  intro a b same
  cases a <;> cases b <;> first | rfl | exact (p.outer_predecessors_distinct same).elim |
    exact (p.outer_predecessors_distinct same.symm).elim

theorem operands_arguments {Γ Δ : List Width} (args : Operands Γ Δ) : operands (arguments args) = args :=
  Proofs.operands_arguments args

variable (rows : Rows p)

/-- Recover the original scoped operand list in its original order. -/
theorem edge_eq (taken : Bool) : edge rows taken = ⟨.site p.stop, rows.operands taken⟩ := by
  change (⟨.site p.stop, operands (arguments (rows.operands taken))⟩ : Edge (Label regs out size) _) = _
  rw [operands_arguments]

/-- Read back the exact actual edge, including every scoped operand in order. -/
theorem edge_is_actual (taken : Bool) :
    successor (p.outerEdgeOccurrence taken).2 (terminal (predecessor p taken)).2 = some (edge rows taken) := by
  rw [edge_eq]
  exact (Proofs.checked_successor _ _ (rows.checked taken)).1

/-- A second slot in either of these actual emitted predecessors cannot
enter the first outer-tail block. The inspection here checks the destination
of the raw successor, including the other slot of a conditional. -/
theorem other_slot_excluded (taken : Bool) (other : Fin 2) (different : other ≠ (p.outerEdgeOccurrence taken).2) :
    (successor other (terminal (predecessor p taken)).2).bind (atTarget p.stop) = none := by
  obtain ⟨actual, _⟩ := readRows_exists p
  exact (Proofs.checked_successor _ _ (actual.checked taken)).2 other different

/-- Recovering operands through Φ and evaluating them reads the original
whole typed operand packet in the same local environment. -/
theorem readBank_eq (taken : Bool) (old : Env (Scope p taken)) :
    readBank rows taken old = (rows.operands taken).eval old := by
  change (operands (arguments (rows.operands taken))).eval old = _
  rw [operands_arguments]

theorem checkBanks_iff (old : (taken : Bool) → Env (Scope p taken))
    (proposed : Bool → Env (Widths regs)) :
    checkBanks rows old proposed = true ↔
      ∀ taken, (rows.operands taken).eval (old taken) = proposed taken := by
  simp only [checkBanks, Bool.and_eq_true, Proofs.sameBank_iff, readBank_eq]
  exact ⟨fun both taken => Bool.casesOn taken both.2 both.1, fun every => ⟨every true, every false⟩⟩

/-- The entry bank recovered from the reached CF slot is the bank returned
by the actual numbered outer γ, before either executes the shared tail. -/
theorem numbered_readBank (input old : Bank (regs := regs) model) (fuel : Nat) :
    ((Outer.Numbered.outerRegion p).toGraph.run (Join.model model) fuel old).map (encodeValues (ins := regs)) =
      some (readBank rows (arrivalSide (p := p) old) (arrivalEnv (p := p) input old)) := by
  rw [Outer.Numbered.outer_run, readBank_eq]
  exact congrArg some (rows.selected_bank input old).symm

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Readback
