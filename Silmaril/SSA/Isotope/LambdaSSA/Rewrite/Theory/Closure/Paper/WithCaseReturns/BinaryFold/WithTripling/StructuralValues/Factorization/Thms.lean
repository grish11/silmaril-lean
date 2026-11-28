module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.StructuralValues.Factorization.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingProjectionSquare

/-! # A composite of structural projections with no intermediate square -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.ProjectionSquare

open CategoryTheory CategoryTheory.Limits
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton (ofType pairArrows pairing_fst_of_discard fst_discard)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.StructuralValues (HomProperty fst_mem)

universe u v w
variable {κ : Type u} {Φ : Type v} [HasTy Φ (Ty κ)] {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "T" => Step (τ := Ty κ) (Φ := Φ) pe
set_option hygiene false in
local notation "Obj" => ofType T
local notation "Bit" => (Silmaril.coprod (Silmaril.unit : Ty κ) Silmaril.unit)
local notation "Pair" => (Silmaril.product Bit Bit)

theorem first_mem : HomProperty T (first pe) := fst_mem T Pair Bit

theorem second_mem : HomProperty T (second pe) := fst_mem T Bit Bit

/-- Both first projections have typed sections in the same quotient. -/
theorem first_split :
    ∃ s : Obj Pair ⟶ Obj (Silmaril.product Pair Bit), s ≫ first pe = 𝟙 _ :=
  ⟨pairArrows T (𝟙 _) (second pe), pairing_fst_of_discard T _ _ (fst_discard T Bit Bit)⟩

theorem second_split : ∃ s : Obj Bit ⟶ Obj Pair, s ≫ second pe = 𝟙 _ :=
  ⟨pairArrows T (𝟙 _) (𝟙 _), pairing_fst_of_discard T _ _ (Category.id_comp _)⟩

/-- The two projections together preserve the typed transition. -/
theorem composite_square :
    sourceStep pe ≫ coprod.map (𝟙 (Obj Pair)) (first pe ≫ second pe) =
      (first pe ≫ second pe) ≫ targetStep pe :=
  TriplingProjectionSquare.composite_square pe

/-- Even the first square fails for every possible intermediate round in the
quotient. Its next visible pair would need the bit that this projection drops. -/
theorem no_intermediate_left (m : Obj Pair ⟶ Obj Pair ⨿ Obj Pair) :
    sourceStep pe ≫ coprod.map (𝟙 (Obj Pair)) (first pe) ≠ first pe ≫ m :=
  TriplingProjectionSquare.no_intermediate_left pe m

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.ProjectionSquare
