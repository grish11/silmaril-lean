module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Blocks.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SwitchingDoubling

/-! # Double iteration of a native two-state switch -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {X Y B : τ}

local notation "Obj" => ofType (Φ := Φ)
local notation "S" => Obj (Silmaril.coprod X Y)

/-- Restrict the actual doubled step to each summand. An exit on the
first row goes directly to the shared result port. A repeat runs the
opposite row, which can also exit. -/
theorem switching_double_rows (g : S ⟶ Obj B ⨿ S)
    (left : Obj X ⟶ Obj B ⨿ Obj Y) (right : Obj Y ⟶ Obj B ⨿ Obj X)
    (hl : (sumCofan X Y).inl ≫ g = left ≫ coprod.map (𝟙 (Obj B)) (sumCofan X Y).inr)
    (hr : (sumCofan X Y).inr ≫ g = right ≫ coprod.map (𝟙 (Obj B)) (sumCofan X Y).inl) :
    let doubled := g ≫ coprod.desc coprod.inl g
    (sumCofan X Y).inl ≫ doubled =
      (left ≫ coprod.desc coprod.inl right) ≫ coprod.map (𝟙 (Obj B)) (sumCofan X Y).inl ∧
    (sumCofan X Y).inr ≫ doubled =
      (right ≫ coprod.desc coprod.inl left) ≫ coprod.map (𝟙 (Obj B)) (sumCofan X Y).inr :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SwitchingDoubling.switching_double_rows g left right hl hr

/-- A typed two-summand step can exit or recur in the opposite summand.
The single and doubled iterates agree in standard Paper. -/
theorem iterate_double_of_switching_rows_with_exit (g : S ⟶ Obj B ⨿ S)
    (left : Obj X ⟶ Obj B ⨿ Obj Y) (right : Obj Y ⟶ Obj B ⨿ Obj X)
    (hl : (sumCofan X Y).inl ≫ g = left ≫ coprod.map (𝟙 (Obj B)) (sumCofan X Y).inr)
    (hr : (sumCofan X Y).inr ≫ g = right ≫ coprod.map (𝟙 (Obj B)) (sumCofan X Y).inl) :
    iterate (g ≫ coprod.desc coprod.inl g) = iterate g :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SwitchingDoubling.iterate_double_of_switching_rows_with_exit
    g left right hl hr

/-- When both native rows repeat into the opposite summand, the single
and doubled iterates agree. The row arrows can execute arbitrary effects. -/
theorem iterate_double_of_switching_rows (g : S ⟶ Obj B ⨿ S)
    (left : Obj X ⟶ Obj Y) (right : Obj Y ⟶ Obj X)
    (hl : (sumCofan X Y).inl ≫ g = left ≫ (sumCofan X Y).inr ≫ coprod.inr)
    (hr : (sumCofan X Y).inr ≫ g = right ≫ (sumCofan X Y).inl ≫ coprod.inr) :
    iterate (g ≫ coprod.desc coprod.inl g) = iterate g :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SwitchingDoubling.iterate_double_of_switching_rows g left right hl hr

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
