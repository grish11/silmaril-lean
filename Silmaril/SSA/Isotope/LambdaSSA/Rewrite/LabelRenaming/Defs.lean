module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Defs

/-! # Maps of interpreted λSSA label contexts -/

@[expose] public section

universe v u w

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)

variable {V : Type u} [Category.{v} V] [CartesianMonoidalCategory V]
  [HasFiniteCoproducts V] {τ : Type w} [TypeFormers τ]

omit [TypeFormers τ] in
/-- Regard the type at a finite label index as a typed lookup. -/
theorem labelAt_get (L : LCtx τ) (i : Fin L.length) : At L i (L.get i) := by
  simp [At, i.isLt]

/-- A type-preserving label renaming maps each exit summand to its renamed injection. -/
noncomputable def labelMap (M : TypeModel τ V) {L K : LCtx τ} {ρ : Nat → Nat}
    (hρ : Ren L K ρ) : labelObj M L ⟶ labelObj M K :=
  Sigma.desc fun i => labelInject M (ρ i) (hρ (labelAt_get L i))

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
