module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Doubling.Switching.Thms

/-! # Two rows with self recurrence confined to the left summand -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.OneSidedSwitch

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {X Y B : τ}

local notation "Obj" => ofType (Φ := Φ)
local notation "S" => Obj (Silmaril.coprod X Y)
local notation "Exit" => Obj B
local notation "Ports" => (Exit ⨿ Obj X) ⨿ Obj Y

/-- The left row may exit, recur to the left, or switch to the right.
The right row may exit or switch to the left. -/
noncomputable def step (left : Obj X ⟶ Ports) (right : Obj Y ⟶ Exit ⨿ Obj X) : S ⟶ Exit ⨿ S :=
  blockCopair left (right ≫ coprod.inl) ≫ joinBlockExits X Y Exit

/-- On the second leg, an answer bypasses the row and a left transfer runs it. -/
noncomputable def afterLeft (left : Obj X ⟶ Ports) : Exit ⨿ Obj X ⟶ Ports :=
  coprod.desc (coprod.inl ≫ coprod.inl) left

noncomputable def doubledLeft (left : Obj X ⟶ Ports) (right : Obj Y ⟶ Exit ⨿ Obj X) : Obj X ⟶ Ports :=
  left ≫ coprod.desc (afterLeft left) (right ≫ coprod.inl)

noncomputable def doubledRight (left : Obj X ⟶ Ports) (right : Obj Y ⟶ Exit ⨿ Obj X) : Obj Y ⟶ Ports :=
  right ≫ afterLeft left

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.OneSidedSwitch
