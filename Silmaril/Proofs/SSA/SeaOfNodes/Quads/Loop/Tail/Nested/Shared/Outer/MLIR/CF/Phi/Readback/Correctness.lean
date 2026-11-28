module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Readback.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Readback.Proofs

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op)
open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Edge)
open Silmaril.MLIR.Pure (Operands)
open Diamond.MLIR.CF (Label Widths)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {p : Program src entry}
variable {Γ Δ : List Width}

private theorem lookup_operand {w : Width} (v : Var Γ w) :
    lookup (operand v).val (operand v).property = v := by
  induction v with
  | here => rfl
  | there v ih =>
    change Var.there (lookup (operand v).val (operand v).property) = .there v
    rw [ih]

theorem operands_arguments (args : Operands Γ Δ) : operands (arguments args) = args := by
  induction args with
  | nil => rfl
  | cons v rest ih =>
    change Operands.cons (lookup (operand v).val (operand v).property) (operands (arguments rest)) =
      .cons v rest
    rw [lookup_operand, ih]

private theorem edge_eq {target : Fin size} (edge : Edge (Label regs out size) Γ)
    (args : Operands Γ (Widths regs)) (checked : atTarget target edge = some args) :
    edge = ⟨.site target, args⟩ := by
  rcases edge with ⟨label, values⟩
  cases label with
  | exit => cases checked
  | site id =>
    simp only [atTarget] at checked
    split at checked
    · rename_i same
      subst id
      cases Option.some.inj checked
      rfl
    · cases checked

private theorem different_zero {slot other : Fin 2} (nonzero : slot ≠ 0) (different : other ≠ slot) :
    other = 0 := by
  simp only [Fin.ext_iff, Fin.val_zero] at nonzero different ⊢
  omega

theorem checked_successor {target : Fin size} {slot : Fin 2}
    (term : Silmaril.MLIR.CF.Terminator (Label regs out size) Δ Γ)
    (args : Operands Γ (Widths regs)) (checked : atSlot target slot term = some args) :
    successor slot term = some ⟨.site target, args⟩ ∧
      ∀ other, other ≠ slot → (successor other term).bind (atTarget target) = none := by
  cases term with
  | ret => cases checked
  | br edge =>
    by_cases zero : slot = 0
    · simp only [atSlot, ite_eq_left zero] at checked
      have same := edge_eq edge args checked
      refine ⟨by simp [successor, zero, same], fun other different => ?_⟩
      simp [successor, show other ≠ 0 from zero ▸ different]
    · simp [atSlot, zero] at checked
  | condBr _ yes no =>
    by_cases zero : slot = 0
    · simp only [atSlot, ite_eq_left zero] at checked
      split at checked
      · rename_i absent
        refine ⟨by simp [successor, zero, edge_eq yes args checked], fun other different => ?_⟩
        simp [successor, show other ≠ 0 from zero ▸ different, Option.isNone_iff_eq_none.mp absent]
      · cases checked
    · simp only [atSlot, ite_eq_right zero] at checked
      split at checked
      · rename_i absent
        refine ⟨by simp [successor, zero, edge_eq no args checked], fun other different => ?_⟩
        simp [successor, different_zero zero different, Option.isNone_iff_eq_none.mp absent]
      · cases checked

theorem sameBank_iff (actual expected : Env Δ) : sameBank actual expected = true ↔ actual = expected := by
  induction actual with
  | nil => cases expected; simp [sameBank]
  | cons value rest ih =>
    cases expected
    simp [sameBank, ih]

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Readback.Proofs
