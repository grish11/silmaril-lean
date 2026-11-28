module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Products.Thms

/-! # Forgetting the last two fields of a three-bit state -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.ProjectionSquare

open CategoryTheory CategoryTheory.Limits
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
  (ofType productFst productSnd pairArrows)

universe u v w
variable {κ : Type u} {Φ : Type v} [HasTy Φ (Ty κ)] {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "T" => Step (τ := Ty κ) (Φ := Φ) pe
set_option hygiene false in
local notation "Obj" => ofType T
local notation "Bit" => (Silmaril.coprod (Silmaril.unit : Ty κ) Silmaril.unit)
local notation "Pair" => (Silmaril.product Bit Bit)
local notation "State" => (Silmaril.product Pair Bit)

abbrev first : Obj State ⟶ Obj Pair := productFst T Pair Bit

abbrev second : Obj Pair ⟶ Obj Bit := productFst T Bit Bit

abbrev hidden : Obj State ⟶ Obj Bit := productSnd T Pair Bit

/-- On repeat, copy the hidden bit into the second component of the pair. -/
noncomputable def next : Obj State ⟶ Obj State :=
  pairArrows T (pairArrows T (first pe ≫ second pe) (hidden pe)) (hidden pe)

/-- Both rounds have the same outward type. The source runs the update and
the target repeats the retained first bit. -/
noncomputable def sourceStep : Obj State ⟶ Obj Pair ⨿ Obj State := next pe ≫ coprod.inr

noncomputable def targetStep : Obj Bit ⟶ Obj Pair ⨿ Obj Bit := coprod.inr

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.ProjectionSquare
