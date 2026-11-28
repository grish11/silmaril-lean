module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Defs

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply

open Isotope.LetCase.LocallyNameless (AbortEquiv Equiv HasType Refinement)

set_option backward.isDefEq.respectTransparency false

local notation "Γ₀" => (Ctx.nil : Ctx Empty Sorts)
local notation "U" => (Ty.unit : Sorts)

theorem normalize_operand_proof {R : Type} {A : Sorts} (ret : ReturnOperand R A)
    (p : Tree R) {n : Nat} (β : BoundCtx Sorts n) :
    AbortEquiv false Γ₀ β (p.operandWith ret β).1 (p.normal.render.operandWith ret β).1 A := by
  induction p generalizing n with
  | ret r => exact .equiv (.refl (ret β r).2.toHasType)
  | emit bit next ih => exact .let₁ (.equiv (.refl (.op .unit))) (ih (β.snoc U))
  | stop fault sequenced =>
    cases sequenced
    · exact .equiv (.refl (.abort (.op .unit)))
    · let d : HasType signature.Instr Γ₀ β (.op (.stop fault) .unit) Ty.empty := .op .unit
      exact (AbortEquiv.sequence (pe := false) (A := A) d).symm
  | ask req bound l r ihl ihr =>
    let d : HasType signature.Instr Γ₀ β (.op (.ask req) .unit) Answer := .op .unit
    have normalize := Refinement.case (.equiv (.refl d)) (ihl (β.snoc U)) (ihr (β.snoc U))
    cases bound
    · exact normalize
    · have once := Equiv.bindCase (pureEff := false) d
        (l.operandWith ret (β.snoc U)).2.toHasType (r.operandWith ret (β.snoc U)).2.toHasType
      exact .trans (.equiv once.symm) normalize

theorem repaired_of_normal_proof (tail : List Sorts) (p q : Tree) (h : p.normal = q.normal) :
    Repaired false (equation tail p q) := by
  have left := normalize_operand_proof unitReturn p .nil
  rw [h] at left
  exact .let₁ (left.trans (normalize_operand_proof unitReturn q .nil).symm)
    (.equiv (.refl (.let₁ .bv (.inl .bv))))

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply
