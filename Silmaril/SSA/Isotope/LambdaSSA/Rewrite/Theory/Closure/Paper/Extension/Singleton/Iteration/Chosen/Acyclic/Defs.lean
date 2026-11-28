module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Defs

/-! # Guarded steps with a finite acyclic decomposition -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed

/-- A bottom stratum only exits. Every added stratum may exit or transfer
to one of the earlier strata. The row computations are arbitrary. -/
inductive AcyclicStep (B : Q) : {A : Q} → (A ⟶ B ⨿ A) → Prop where
  | exits {A : Q} (f : A ⟶ B) : AcyclicStep B (f ≫ coprod.inl)
  | extend {A X Y : Q} (split : X ≅ A ⨿ Y) {f : A ⟶ B ⨿ A} (row : Y ⟶ B ⨿ A) :
      AcyclicStep B f →
      AcyclicStep B (split.hom ≫ coprod.desc f row ≫ coprod.map (𝟙 B) (coprod.inl ≫ split.inv))

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
