module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Doubling.Switching.OneSided.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OneSidedDoubling

/-! # The residual equations for one-sided switching -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.OneSidedSwitch

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {X Y B : τ}

local notation "Obj" => ofType (Φ := Φ)
local notation "S" => Obj (Silmaril.coprod X Y)
local notation "Exit" => Obj B
local notation "Ports" => (Exit ⨿ Obj X) ⨿ Obj Y

/-- Exact rows of the written doubled step, before eliminating either block. -/
theorem doubled_eq (left : Obj X ⟶ Ports) (right : Obj Y ⟶ Exit ⨿ Obj X) :
    step left right ≫ coprod.desc coprod.inl (step left right) =
      blockCopair (doubledLeft left right) (doubledRight left right) ≫ joinBlockExits X Y Exit :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OneSidedDoubling.doubled_eq left right

/-- Eliminate the no-self row of the single step by exposing left transfers as local exits. -/
theorem iterate_step (left : Obj X ⟶ Ports) (right : Obj Y ⟶ Exit ⨿ Obj X) :
    let cut := left ≫ coprod.desc (𝟙 (Exit ⨿ Obj X)) right
    iterate (step left right) = blockCopair (iterate cut) (right ≫ coprod.desc (𝟙 Exit) (iterate cut)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OneSidedDoubling.iterate_step left right

/-- The two local obligations after elimination are exact. The left cuts must have equal iterates, and the right cut must agree with the original right row when transfers to the left are run to completion. -/
theorem iterate_double_iff (left : Obj X ⟶ Ports) (right : Obj Y ⟶ Exit ⨿ Obj X) :
    let cut := left ≫ coprod.desc (𝟙 (Exit ⨿ Obj X)) right
    let rightCut := iterate (doubledRight left right)
    let doubleCut := doubledLeft left right ≫ coprod.desc (𝟙 (Exit ⨿ Obj X)) rightCut
    iterate (step left right ≫ coprod.desc coprod.inl (step left right)) = iterate (step left right) ↔
      iterate doubleCut = iterate cut ∧
      rightCut ≫ coprod.desc (𝟙 Exit) (iterate cut) = right ≫ coprod.desc (𝟙 Exit) (iterate cut) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OneSidedDoubling.iterate_double_iff left right

/-- If the left row stays in the left summand, the comparison contains the arbitrary native doubling equation on that summand. -/
theorem embedded_double_iff (row : Obj X ⟶ Exit ⨿ Obj X) (right : Obj Y ⟶ Exit ⨿ Obj X) :
    let g := step (row ≫ coprod.inl) right
    iterate (g ≫ coprod.desc coprod.inl g) = iterate g ↔
      iterate (row ≫ coprod.desc coprod.inl row) = iterate row :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OneSidedDoubling.embedded_double_iff row right

/-- Transport the actual native iterate through an exact change of state coordinates. -/
theorem iterate_regrouping {Z : τ}
    (g : S ⟶ Exit ⨿ S) (h : Obj Z ⟶ Exit ⨿ Obj Z) (e : S ≅ Obj Z)
    (square : g ≫ coprod.map (𝟙 Exit) e.hom = e.hom ≫ h) :
    iterate g = e.hom ≫ iterate h :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OneSidedDoubling.iterate_regrouping g h e square

/-- An exact change of state coordinates preserves doubling. In particular,
a step that becomes a two-summand switch in the new coordinates satisfies
doubling by `iterate_double_of_switching_rows_with_exit`. The exit object
is fixed by the change of coordinates. -/
theorem iterate_double_of_regrouping {Z : τ}
    (g : S ⟶ Exit ⨿ S) (h : Obj Z ⟶ Exit ⨿ Obj Z) (e : S ≅ Obj Z)
    (square : g ≫ coprod.map (𝟙 Exit) e.hom = e.hom ≫ h)
    (doubles : iterate (h ≫ coprod.desc coprod.inl h) = iterate h) :
    iterate (g ≫ coprod.desc coprod.inl g) = iterate g :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OneSidedDoubling.iterate_double_of_regrouping g h e square doubles

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.OneSidedSwitch
