module

public import Silmaril.SSA.Isotope.LetCase.HandledTrace.Defs
public import Silmaril.Semantics.ITree.Trace.Handled.Thms
import Silmaril.Proofs.SSA.Isotope.LetCase.HandledTrace.Sequencing

public section

namespace Silmaril.Isotope.LetCase.LocallyNameless.Derivation

open Silmaril.Elgot.ITree Silmaril.Isotope.Semantics

universe u w q e s

variable {τ : Type u} [TypeFormers τ] {D : τ → Type (e + 1)}
  [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {ν : Type w} [DecidableEq ν] {Φ : Type q} [HasTy Φ τ]
  {Events : Type e → Type e} {X : Type s} {step : Handler X Events} {x : X}
  {M : InstructionModel D Φ (Tree Events)} {n : Nat} {Γ : Ctx ν τ} {β : BoundCtx τ n}
  {γ : FreeEnv D Γ} {ρ : BoundEnv D β}

/-- A typed let compares continuations in the same ambient environment with
the reached value in the newest slot and the reached handler state for replay. -/
theorem handledTraceLE_let₁ {a a' : Tm ν Φ n} {b b' : Tm ν Φ (n + 1)} {A B : τ}
    {da : Derivation Φ Γ β a A} {da' : Derivation Φ Γ β a' A}
    {db : Derivation Φ Γ (β.snoc A) b B} {db' : Derivation Φ Γ (β.snoc A) b' B}
    (producer : HandledTraceLE step x (da.denote D M γ ρ) (da'.denote D M γ ρ))
    (body : ∀ {y value}, ReturnsTo step x (da.denote D M γ ρ) y value →
      HandledTraceLE step y (db.denote D M γ (ρ.snoc value)) (db'.denote D M γ (ρ.snoc value))) :
    HandledTraceLE step x ((Derivation.let₁ da db).denote D M γ ρ)
      ((Derivation.let₁ da' db').denote D M γ ρ) :=
  producer.bind body

/-- A typed case uses the original sum tag to pick the arm. Only reachable
typed payloads are needed, with the original captures and replay state. -/
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
      ((Derivation.case da' dl' dr').denote D M γ ρ) :=
  Silmaril.Proofs.SSA.Isotope.LetCase.HandledTrace.handledTraceLE_case scrutinee left right

end Silmaril.Isotope.LetCase.LocallyNameless.Derivation
