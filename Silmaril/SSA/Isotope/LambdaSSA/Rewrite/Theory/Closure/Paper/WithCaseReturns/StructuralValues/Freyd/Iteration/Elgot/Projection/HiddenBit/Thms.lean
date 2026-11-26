module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.StructuralValues.Freyd.Iteration.Elgot.Projection.HiddenBit.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.HiddenBitFeedback

/-! # Hidden-bit projection squares and alternating iteration -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues.HiddenBit

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton
open scoped MonoidalCategory

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.StructuralValues (HomProperty)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {ε : Type w} [HasEff Φ ε] (pe : ε)
local notation "Seed" => Paper.WithCaseReturns.JoinedStep (τ := τ) (Φ := Φ) pe
local notation "Q" => Paper.WithCaseReturns.TypeCategory (τ := τ) (Φ := Φ) pe
local notation "U" => (Silmaril.unit : τ)
local notation "Bit" => Silmaril.coprod U U
local notation "Obj" => ofType Seed

local notation "I" => iterateChosen Seed

/-- First projection corresponds to the fold of the two copies. -/
theorem modes_fst (A : τ) :
    (modes pe A).hom ≫ productFst Seed A Bit = coprod.desc (𝟙 (Obj A)) (𝟙 (Obj A)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.HiddenBitFeedback.modes_fst pe A

/-- The left-tag injection is a section of first projection. -/
theorem leftMode_fst (A : τ) :
    leftMode pe A ≫ productFst Seed A Bit = 𝟙 _ :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.HiddenBitFeedback.leftMode_fst pe A

/-- The projection square consists of the two visible row equations. -/
theorem projection_square_rows (A : τ) {B : Q}
    (f : Obj (product A Bit) ⟶ B ⨿ Obj (product A Bit)) (g : Obj A ⟶ B ⨿ Obj A) :
    let d := rows pe A f
    let flat := coprod.desc (𝟙 (B ⨿ Obj A)) coprod.inr
    f ≫ coprod.map (𝟙 B) (productFst Seed A Bit) = productFst Seed A Bit ≫ g ↔
      (coprod.inl ≫ d) ≫ flat = g ∧ (coprod.inr ≫ d) ≫ flat = g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.HiddenBitFeedback.projection_square_rows pe A f g

/-- Eliminate the right mode to express the remaining equality for arbitrary hidden-bit steps. -/
theorem hidden_bit_reset_iff_mixed (A : τ) {B : Q}
    (f : Obj (product A Bit) ⟶ B ⨿ Obj (product A Bit)) (g : Obj A ⟶ B ⨿ Obj A)
    (square : f ≫ coprod.map (𝟙 B) (productFst Seed A Bit) = productFst Seed A Bit ≫ g) :
    let d := rows pe A f
    I f = I (f ≫ coprod.map (𝟙 B) (productFst Seed A Bit ≫ leftMode pe A)) ↔
      I ((coprod.inl ≫ d) ≫ coprod.desc (𝟙 (B ⨿ Obj A)) (I (coprod.inr ≫ d))) = I g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.HiddenBitFeedback.hidden_bit_reset_iff_mixed pe A f g square

/-- The alternating step commutes with first projection in the computation quotient. -/
theorem flipStep_square (A : τ) {B : Q} (g : Obj A ⟶ B ⨿ Obj A) :
    flipStep pe A g ≫ coprod.map (𝟙 B) (productFst Seed A Bit) = productFst Seed A Bit ≫ g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.HiddenBitFeedback.flipStep_square pe A g

/-- A repeat from the left mode enters the right mode. -/
theorem flipStep_left (A : τ) {B : Q} (g : Obj A ⟶ B ⨿ Obj A) :
    leftMode pe A ≫ flipStep pe A g = g ≫ coprod.map (𝟙 B) (rightMode pe A) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.HiddenBitFeedback.flipStep_left pe A g

/-- A repeat from the right mode enters the left mode. -/
theorem flipStep_right (A : τ) {B : Q} (g : Obj A ⟶ B ⨿ Obj A) :
    rightMode pe A ≫ flipStep pe A g = g ≫ coprod.map (𝟙 B) (leftMode pe A) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.HiddenBitFeedback.flipStep_right pe A g

/-- Folding the two summands commutes with the alternating step. -/
theorem alternating_fold_square {A B : Q} (g : A ⟶ B ⨿ A) :
    alternatingStep pe g ≫ coprod.map (𝟙 B) (coprod.desc (𝟙 A) (𝟙 A)) =
      coprod.desc (𝟙 A) (𝟙 A) ≫ g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.HiddenBitFeedback.alternating_fold_square pe g

/-- A fold square is uniform when one mode only recurs into itself.
The other mode can still recur into either mode. -/
theorem binary_fold_of_closed_mode {A B : Q}
    (f : A ⨿ A ⟶ B ⨿ (A ⨿ A)) (g : A ⟶ B ⨿ A)
    (square : f ≫ coprod.map (𝟙 B) (coprod.desc (𝟙 A) (𝟙 A)) =
      coprod.desc (𝟙 A) (𝟙 A) ≫ g)
    (closed :
      coprod.inl ≫ f = g ≫ coprod.map (𝟙 B) (coprod.inl : A ⟶ A ⨿ A) ∨
      coprod.inr ≫ f = g ≫ coprod.map (𝟙 B) (coprod.inr : A ⟶ A ⨿ A)) :
    I f = coprod.desc (𝟙 A) (𝟙 A) ≫ I g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.HiddenBitFeedback.TwoMode.binary_fold_of_closed_mode
    Seed f g square closed

/-- A closed mode can be eliminated in any contextual quotient. -/
theorem binary_fold_of_closed_mode_of_seed
    (S : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
    {A B : Extension.Singleton.TypeCategory S}
    (f : A ⨿ A ⟶ B ⨿ (A ⨿ A)) (g : A ⟶ B ⨿ A)
    (square : f ≫ coprod.map (𝟙 B) (coprod.desc (𝟙 A) (𝟙 A)) =
      coprod.desc (𝟙 A) (𝟙 A) ≫ g)
    (closed :
      coprod.inl ≫ f = g ≫ coprod.map (𝟙 B) (coprod.inl : A ⟶ A ⨿ A) ∨
      coprod.inr ≫ f = g ≫ coprod.map (𝟙 B) (coprod.inr : A ⟶ A ⨿ A)) :
    iterateChosen S f = coprod.desc (𝟙 A) (𝟙 A) ≫ iterateChosen S g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.HiddenBitFeedback.TwoMode.binary_fold_of_closed_mode
    S f g square closed

/-- After eliminating the right mode, the remaining iteration equation is
equivalent to uniformity of the binary fold. -/
theorem binary_fold_iff_mixed_of_seed
    (S : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
    {A B : Extension.Singleton.TypeCategory S}
    (f : A ⨿ A ⟶ (B ⨿ A) ⨿ A) (g : A ⟶ B ⨿ A)
    (right : (coprod.inr ≫ f) ≫ coprod.desc (𝟙 (B ⨿ A)) coprod.inr = g) :
    iterateChosen S (f ≫ (coprod.associator B A A).hom) =
      coprod.desc (𝟙 A) (𝟙 A) ≫ iterateChosen S g ↔
      iterateChosen S ((coprod.inl ≫ f) ≫ coprod.desc (𝟙 (B ⨿ A))
        (iterateChosen S (coprod.inr ≫ f))) = iterateChosen S g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.HiddenBitFeedback.TwoMode.iterate_iff_mixed
    S f g right

/-- When the right mode always switches on recurrence, doubling the left
row at its enlarged outward coproduct suffices for fold uniformity. -/
theorem binary_fold_of_right_switch_and_double {A B : Q}
    (f : A ⨿ A ⟶ B ⨿ (A ⨿ A)) (g : A ⟶ B ⨿ A)
    (square : f ≫ coprod.map (𝟙 B) (coprod.desc (𝟙 A) (𝟙 A)) =
      coprod.desc (𝟙 A) (𝟙 A) ≫ g)
    (switch : coprod.inr ≫ f = g ≫ coprod.map (𝟙 B) (coprod.inl : A ⟶ A ⨿ A))
    (double :
      let p := (coprod.inl ≫ f) ≫ (coprod.associator B A A).inv
      I (p ≫ coprod.desc coprod.inl p) = I p) :
    I f = coprod.desc (𝟙 A) (𝟙 A) ≫ I g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.HiddenBitFeedback.TwoMode.binary_fold_of_right_switch_and_double
    Seed f g square switch double

/-- The right-switch argument uses only the chosen quotient iteration laws. -/
theorem binary_fold_of_right_switch_and_double_of_seed
    (S : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
    {A B : Paper.Extension.Singleton.TypeCategory S}
    (f : A ⨿ A ⟶ B ⨿ (A ⨿ A)) (g : A ⟶ B ⨿ A)
    (square : f ≫ coprod.map (𝟙 B) (coprod.desc (𝟙 A) (𝟙 A)) =
      coprod.desc (𝟙 A) (𝟙 A) ≫ g)
    (switch : coprod.inr ≫ f = g ≫ coprod.map (𝟙 B) (coprod.inl : A ⟶ A ⨿ A))
    (double :
      let p := (coprod.inl ≫ f) ≫ (coprod.associator B A A).inv
      iterateChosen S (p ≫ coprod.desc coprod.inl p) = iterateChosen S p) :
    iterateChosen S f = coprod.desc (𝟙 A) (𝟙 A) ≫ iterateChosen S g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.HiddenBitFeedback.TwoMode.binary_fold_of_right_switch_and_double
    S f g square switch double

/-- The alternating reduction uses the same chosen iteration in any contextual quotient. -/
theorem alternating_fold_iff_double_of_seed
    (S : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
    {A B : Paper.Extension.Singleton.TypeCategory S} (g : A ⟶ B ⨿ A) :
    iterateChosen S (coprod.desc (g ≫ coprod.map (𝟙 B) coprod.inr)
      (g ≫ coprod.map (𝟙 B) coprod.inl)) =
        coprod.desc (𝟙 A) (𝟙 A) ≫ iterateChosen S g ↔
      iterateChosen S (g ≫ coprod.desc coprod.inl g) = iterateChosen S g := by
  have alt := coprod.hom_ext
    ((Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.HiddenBitFeedback.TwoMode.alternate_row_routes S g).1.trans (coprod.inl_desc _ _).symm)
    ((Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.HiddenBitFeedback.TwoMode.alternate_row_routes S g).2.trans (coprod.inr_desc _ _).symm)
  rw [← alt]
  exact Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.HiddenBitFeedback.TwoMode.alternate_uniform_iff S g

/-- Uniformity for the binary fold on an alternating step is exactly the double-step equation. -/
theorem alternating_fold_iff_double {A B : Q} (g : A ⟶ B ⨿ A) :
    I (alternatingStep pe g) = coprod.desc (𝟙 A) (𝟙 A) ≫ I g ↔
      I (g ≫ coprod.desc coprod.inl g) = I g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.HiddenBitFeedback.alternating_fold_iff_double pe g

/-- Reset invariance for the alternating step is equivalent to the double-step iteration equation. -/
theorem flipStep_reset_iff (A : τ) {B : Q} (g : Obj A ⟶ B ⨿ Obj A) :
    I (flipStep pe A g) = I (flipStep pe A g ≫
      coprod.map (𝟙 B) (productFst Seed A Bit ≫ leftMode pe A)) ↔
      I (g ≫ coprod.desc coprod.inl g) = I g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.HiddenBitFeedback.flipStep_reset_iff pe A g

/-- The alternating repeat has the exact structural projection square and preserves iteration under reset. -/
theorem always_repeat_flip_reset (A : τ) (B : Q) :
    let g : Obj A ⟶ B ⨿ Obj A := coprod.inr
    let f := flipStep pe A g
    let p := productFst Seed A Bit
    HomProperty Seed p ∧
      (leftMode pe A ≫ f = rightMode pe A ≫ coprod.inr) ∧
      (rightMode pe A ≫ f = leftMode pe A ≫ coprod.inr) ∧
      f ≫ coprod.map (𝟙 B) p = p ≫ g ∧
      I f = I (f ≫ coprod.map (𝟙 B) (p ≫ leftMode pe A)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.HiddenBitFeedback.always_repeat_flip_reset pe A B

/-- If the doubled step has no repeat, its iteration agrees with the original step. -/
theorem iterate_double_of_no_repeat {A B : Q} (g : A ⟶ B ⨿ A) (k : A ⟶ B)
    (noRepeat : g ≫ coprod.desc coprod.inl g = k ≫ coprod.inl) :
    I (g ≫ coprod.desc coprod.inl g) = I g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.HiddenBitFeedback.iterate_double_of_no_repeat pe g k noRepeat

/-- If two visible steps always exit, resetting the hidden bit preserves alternating feedback. -/
theorem flipStep_reset_of_no_repeat (A : τ) {B : Q} (g : Obj A ⟶ B ⨿ Obj A) (k : Obj A ⟶ B)
    (noRepeat : g ≫ coprod.desc coprod.inl g = k ≫ coprod.inl) :
    I (flipStep pe A g) = I (flipStep pe A g ≫
      coprod.map (𝟙 B) (productFst Seed A Bit ≫ leftMode pe A)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.HiddenBitFeedback.flipStep_reset_of_no_repeat pe A g k noRepeat

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues.HiddenBit
