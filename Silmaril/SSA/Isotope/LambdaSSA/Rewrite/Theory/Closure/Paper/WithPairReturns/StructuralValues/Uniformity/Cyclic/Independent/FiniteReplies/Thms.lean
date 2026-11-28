module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FiniteReplyFold

/-! # A quotient square reflects to the erased native rows -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies

open CategoryTheory CategoryTheory.Limits
open Extension.Singleton (iterateChosen)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

universe u

variable {Φ : Type} [Profile Φ]

local notation "X" => unitObj Φ
local notation "U" => nativeUnit Φ
local notation "drop" => Paper.TypeCategory.discardArrow (Φ := Φ) (Silmaril.coprod UnitTy UnitTy)

/-- Sequencing a native arrow after a reply dispatch sequences it after each arm. -/
theorem dispatch_comp {Y Z : Native Φ} (s : ReplyShape) (k : s.Value → (U ⟶ Y)) (f : Y ⟶ Z) :
    dispatch s k ≫ f = dispatch s (fun x => k x ≫ f) :=
  FiniteReplyFold.dispatch_comp s k f

/-- The exact typed reply set of each shape is finite. -/
theorem ReplyShape.finite (s : ReplyShape) : Finite s.Value :=
  let _ : Finite s.Code := FiniteReplyFold.code_finite s
  Finite.of_surjective s.replyEquiv s.replyEquiv.surjective

/-- On the supported row representatives, equality recovers the complete
tree of opcodes, replies, and exit versus recurrence. -/
theorem target_injective : Function.Injective (targetStep (Φ := Φ)) :=
  FiniteReplyFold.target_injective

/-- Folding the actual joined square erases only the destination copy. -/
theorem square_iff_codes (left right : Row Φ Route) (target : Row Φ Bool) :
    sourceStep left right ≫ coprod.map (𝟙 X) fold = fold ≫ targetStep target ↔
      left.map Route.recurrent = target ∧ right.map Route.recurrent = target :=
  FiniteReplyFold.square_iff left right target

/-- The actual quotient square suffices for equality of both fixed erased
row representatives in standard Paper. -/
theorem square_iff_native_rows (left right : Row Φ Route) (target : Row Φ Bool) :
    sourceStep left right ≫ coprod.map (𝟙 X) fold = fold ≫ targetStep target ↔
      left.render nativeRoute ≫ coprod.map (𝟙 U) drop = target.render nativeTarget ∧
      right.render nativeRoute ≫ coprod.map (𝟙 U) drop = target.render nativeTarget :=
  FiniteReplyFold.square_iff_native left right target

/-- Replaying constructor discard on the native rows proves iteration
equality in the ordered-pair quotient. -/
theorem uniformity (left right : Row Φ Route) (target : Row Φ Bool)
    (square : sourceStep left right ≫ coprod.map (𝟙 X) fold = fold ≫ targetStep target) :
    iterateChosen (Seed Φ) (sourceStep left right) = fold ≫ iterateChosen (Seed Φ) (targetStep target) :=
  FiniteReplyFold.uniformity left right target square

namespace Example

/-- A ternary request, a singleton reply, and a request with no replies can
occur in one commuting square. -/
theorem square :
    sourceStep left right ≫ coprod.map (𝟙 (unitObj Op)) fold = fold ≫ targetStep target :=
  (square_iff_codes left right target).2 ⟨rfl, FiniteReplyFold.example_codes⟩

theorem iteration :
    iterateChosen (Seed Op) (sourceStep left right) = fold ≫ iterateChosen (Seed Op) (targetStep target) :=
  uniformity left right target square

end Example

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies
