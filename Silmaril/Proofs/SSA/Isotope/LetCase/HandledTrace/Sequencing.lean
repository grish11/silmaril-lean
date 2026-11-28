module

public import Silmaril.SSA.Isotope.LetCase.HandledTrace.Defs
public import Silmaril.Semantics.ITree.Trace.Handled.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LetCase.HandledTrace

open Silmaril Silmaril.Elgot.ITree Silmaril.Isotope Silmaril.Isotope.Semantics
open Silmaril.Isotope.LetCase.LocallyNameless

universe u w q e s

variable {τ : Type u} [TypeFormers τ] {D : τ → Type (e + 1)}
  [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {ν : Type w} [DecidableEq ν] {Φ : Type q} [HasTy Φ τ]
  {Events : Type e → Type e} {X : Type s} {step : Handler X Events} {x : X}
  {M : InstructionModel D Φ (Tree Events)} {n : Nat} {Γ : Ctx ν τ} {β : BoundCtx τ n}
  {γ : FreeEnv D Γ} {ρ : BoundEnv D β}

theorem handledTraceLE_case {a a' : Tm ν Φ n} {l l' r r' : Tm ν Φ (n + 1)} {A B C : τ}
    {da : Derivation Φ Γ β a (coprod A B)} {da' : Derivation Φ Γ β a' (coprod A B)}
    {dl : Derivation Φ Γ (β.snoc A) l C} {dl' : Derivation Φ Γ (β.snoc A) l' C}
    {dr : Derivation Φ Γ (β.snoc B) r C} {dr' : Derivation Φ Γ (β.snoc B) r' C}
    (scrutinee : HandledTraceLE step x (da.denote D M γ ρ) (da'.denote D M γ ρ))
    (left : ∀ {y a}, ReturnsTo step x (da.denote D M γ ρ) y
      ((CoproductModel.coprodEquiv A B).symm (.inl a)) →
      HandledTraceLE step y (dl.denote D M γ (ρ.snoc a)) (dl'.denote D M γ (ρ.snoc a)))
    (right : ∀ {y b}, ReturnsTo step x (da.denote D M γ ρ) y
      ((CoproductModel.coprodEquiv A B).symm (.inr b)) →
      HandledTraceLE step y (dr.denote D M γ (ρ.snoc b)) (dr'.denote D M γ (ρ.snoc b))) :
    HandledTraceLE step x ((Derivation.case da dl dr).denote D M γ ρ)
      ((Derivation.case da' dl' dr').denote D M γ ρ) := by
  refine scrutinee.bind (fun {y value} reached => ?_)
  obtain ⟨tag, rfl⟩ := (CoproductModel.coprodEquiv (D := D) A B).symm.surjective value
  cases tag with
  | inl a => simpa only [Equiv.apply_symm_apply] using left (y := y) (a := a) reached
  | inr b => simpa only [Equiv.apply_symm_apply] using right (y := y) (b := b) reached

end Silmaril.Proofs.SSA.Isotope.LetCase.HandledTrace
