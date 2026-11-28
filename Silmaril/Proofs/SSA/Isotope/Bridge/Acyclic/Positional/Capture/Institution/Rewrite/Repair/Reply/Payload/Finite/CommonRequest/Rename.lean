module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.CommonRequest.Defs

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.CommonRequest

open Isotope.LetCase.LocallyNameless (Tm)
open LambdaSSA (At)
open LambdaSSA.Acyclic (FiniteExit Operand)

set_option backward.isDefEq.respectTransparency false

local notation "U" => (Ty.unit : Sorts)

private def mapSlots {k m n : Nat} {β : BoundCtx Sorts k} {γ : BoundCtx Sorts m}
    (slots : Retained β n) (ρ : BoundCtx.Renaming β γ) : Retained γ n :=
  fun i => ⟨ρ.toFun (slots i).1, (ρ.typed (slots i).1).trans (slots i).2⟩

private theorem map_bind {k m n : Nat} {β : BoundCtx Sorts k} {γ : BoundCtx Sorts m}
    (slots : Retained β n) (ρ : BoundCtx.Renaming β γ) :
    mapSlots slots.bind (ρ.up Bit) = (mapSlots slots ρ).bind := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

private theorem rename_bit {k m : Nat} {β : BoundCtx Sorts k} {γ : BoundCtx Sorts m}
    (ρ : BoundCtx.Renaming β γ) (b : Bool) :
    (bitOperand β b).1.rename ρ.toFun = (bitOperand γ b).1 := by
  cases b <;> rfl

private theorem rename_expr {n : Nat} (e : Expr n) {k m : Nat}
    {β : BoundCtx Sorts k} {γ : BoundCtx Sorts m} (slots : Retained β n)
    (ρ : BoundCtx.Renaming β γ) :
    (e.operand slots).1.rename ρ.toFun = (e.operand (mapSlots slots ρ)).1 := by
  induction e generalizing k m with
  | literal b => exact rename_bit ρ b
  | read i => rfl
  | split l r ihl ihr =>
    let older : Retained (β.snoc U) _ := fun i => slots.weaken U i.succ
    simp only [Expr.operand, Tm.rename_case]
    congr 1
    · exact ihl older (ρ.up U)
    · exact ihr older (ρ.up U)

private theorem rename_tag (L : List Sorts) (i : Nat) {k m : Nat}
    {β : BoundCtx Sorts k} {γ : BoundCtx Sorts m} {A : Sorts} (h : At L i A)
    (a : Operand signature.Instr β A) (b : Operand signature.Instr γ A)
    (ρ : BoundCtx.Renaming β γ) (eq : a.1.rename ρ.toFun = b.1) :
    (FiniteExit.tag L i h a).1.rename ρ.toFun = (FiniteExit.tag L i h b).1 := by
  induction L generalizing i with
  | nil => cases i <;> contradiction
  | cons B L ih =>
    cases i with
    | zero =>
      have e : B = A := Option.some.inj h
      cases e
      exact congrArg Tm.inl eq
    | succ i => exact congrArg Tm.inr (ih i h)

private theorem rename_request {k m : Nat} {β : BoundCtx Sorts k} {γ : BoundCtx Sorts m}
    {A : Sorts} (ρ : BoundCtx.Renaming β γ) (req bound : Bool)
    (l r : Operand signature.Instr (β.snoc Bit) A)
    (l' r' : Operand signature.Instr (γ.snoc Bit) A)
    (hl : l.1.rename (ρ.up Bit).toFun = l'.1) (hr : r.1.rename (ρ.up Bit).toFun = r'.1) :
    (requestOperand req bound l r).1.rename ρ.toFun = (requestOperand req bound l' r').1 := by
  cases bound <;>
    simp only [requestOperand, Bool.false_eq_true, ite_false, ite_true, Tm.rename_let₁, Tm.rename_case,
      Tm.rename_op, Tm.rename_bv, Tm.rename_unit]
  · rw [show Tm.up ρ.toFun = (ρ.up Bit).toFun from rfl, hl, hr]
  · change Tm.let₁ (.op (.ask req) .unit)
      (.case (.bv 0) (Tm.rename (Tm.up (Tm.up ρ.toFun)) l.1.underBinder)
        (Tm.rename (Tm.up (Tm.up ρ.toFun)) r.1.underBinder)) = _
    rw [Tm.rename_underBinder, Tm.rename_underBinder]
    change Tm.let₁ (.op (.ask req) .unit)
      (.case (.bv 0) (l.1.rename (ρ.up Bit).toFun).underBinder
        (r.1.rename (ρ.up Bit).toFun).underBinder) = _
    rw [hl, hr]

private theorem rename_tree {L : List Sorts} {n : Nat} (p : Tree L n) {k m : Nat}
    {β : BoundCtx Sorts k} {γ : BoundCtx Sorts m} (slots : Retained β n)
    (ρ : BoundCtx.Renaming β γ) :
    (p.operand slots).1.rename ρ.toFun = (p.operand (mapSlots slots ρ)).1 := by
  induction p generalizing k m with
  | ret p e => exact rename_tag L _ p.typed _ _ ρ (rename_expr e slots ρ)
  | emit _ _ ih =>
    simp only [Tree.operand, Tm.rename_let₁, Tm.rename_op, Tm.rename_unit]
    exact congrArg (Tm.let₁ _) (ih (slots.weaken U) (ρ.up U))
  | request req bound l r ihl ihr =>
    have left := ihl slots.bind (ρ.up Bit)
    have right := ihr slots.bind (ρ.up Bit)
    rw [map_bind] at left right
    exact rename_request ρ req bound _ _ _ _ left right
  | testRequest test low lowBound highBound ll lr hl hr ihll ihlr ihhl ihhr =>
    let kept := (slots.without test).weaken U
    have left₁ := ihll kept.bind ((ρ.up U).up Bit)
    have left₂ := ihlr kept.bind ((ρ.up U).up Bit)
    have right₁ := ihhl kept.bind ((ρ.up U).up Bit)
    have right₂ := ihhr kept.bind ((ρ.up U).up Bit)
    rw [map_bind] at left₁ left₂ right₁ right₂
    simp only [Tree.operand, Tm.rename_case]
    congr 1
    · exact rename_request (ρ.up U) low lowBound _ _ _ _ left₁ left₂
    · exact rename_request (ρ.up U) (!low) highBound _ _ _ _ right₁ right₂

theorem operand_underBinder_proof {L : List Sorts} {n k : Nat} (p : Tree L (n + 1))
    {β : BoundCtx Sorts k} (slots : Retained β n) :
    (p.operand slots.bind).1.underBinder = (p.operand (slots.weaken U).bind).1 := by
  have eq := rename_tree p slots.bind ((BoundCtx.Renaming.succ β U).up Bit)
  rw [map_bind] at eq
  exact eq

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.CommonRequest
