module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.Defs

/-! # Maps that merge only two phases of a three-cycle -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle

open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}

local notation "Q" => TypeCategory Seed

/-- Keep one phase separate and merge the other two, keeping their payload. -/
noncomputable def partialFold (A : Q) (keep : Fin 3) : A ⨿ (A ⨿ A) ⟶ A ⨿ A :=
  let leg (i : Fin 3) : A ⟶ A ⨿ A := if i = keep then coprod.inl else coprod.inr
  coprod.desc (leg 0) (coprod.desc (leg 1) (leg 2))

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle
