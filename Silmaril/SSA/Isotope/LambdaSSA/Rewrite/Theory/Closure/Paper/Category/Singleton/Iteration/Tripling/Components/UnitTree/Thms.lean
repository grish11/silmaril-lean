module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.UnitTree.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitTreeTripling
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitTreeTriplingProjection

/-! # Tripling on any finite Unit coproduct -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ComponentTripling

open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "P" => TypeCategory (τ := τ) Φ

/-- Group the three copies of a state by their retained Unit leaf. -/
noncomputable def UnitTree.regroup (t : UnitTree) : Phases (t.obj (τ := τ) (Φ := Φ)) ≅ t.phaseObj :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitTreeTripling.regroup t

/-- The same regrouping at the literal syntax type containing the three phases. -/
noncomputable def UnitTree.regroupExact (t : UnitTree) :
    ofType (Φ := Φ) (UnitTree.ty (τ := τ) (.sum t (.sum t t))) ≅ t.phaseObj :=
  (UnitTree.sum t (.sum t t)).syntaxIso ≪≫ t.regroup

/-- Phase erasure uses a native constructor at every leaf. -/
theorem UnitTree.forget_constructor (t : UnitTree) :
    ConstructorCoproduct (t.forget (τ := τ) (Φ := Φ)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitTreeTripling.forget_tree t

/-- The written round and its three-round batch have the same native
iteration if the Unit payload resets are absorbed at both boundaries. -/
theorem UnitTree.iterate_triple (t : UnitTree) {B : P} (g : t.obj ⟶ B ⨿ t.obj)
    (input : t.reset ≫ g = g) (output : g ≫ coprod.map (𝟙 B) t.reset = g) :
    iterate (thenOnRepeat g (thenOnRepeat g g)) = iterate g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitTreeTripling.iterate_triple t g input output

/-- Inserting literal Unit payload resets gives a native tripling proof
while retaining all recursive and outward port positions. -/
theorem UnitTree.iterate_normalize (t : UnitTree) {B : P} (g : t.obj ⟶ B ⨿ t.obj) :
    iterate (thenOnRepeat (t.normalize g) (thenOnRepeat (t.normalize g) (t.normalize g))) =
      iterate (t.normalize g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitTreeTripling.iterate_normalize t g

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ComponentTripling

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle

open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory.ComponentTripling (UnitTree)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
    (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed

/-- Existing Unit η supplies the payload resets on an arbitrary written
Unit coproduct tree. The exit object and the round's types are exact. -/
theorem triple_step_unit_tree
    (includeUnit : ∀ {Γ L r s}, Paper.WithUnitEta.Step Γ r s L → Seed Γ r s L)
    (t : UnitTree) {B : Q} (g : ofType Seed t.ty ⟶ B ⨿ ofType Seed t.ty) :
    iterateChosen Seed (triple g) = iterateChosen Seed g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitTreeTriplingProjection.triple_step_unit_tree
    Seed includeUnit t g

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle
