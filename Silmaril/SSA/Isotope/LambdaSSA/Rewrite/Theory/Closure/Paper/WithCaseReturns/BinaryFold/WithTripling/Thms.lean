module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldWithTripling

/-! # Exact syntactic tripling in the opt-in quotient -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling

open Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
  (ofType ofRegion projection iterateChosen homRel)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle (triple)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.StructuralValues (inclusion)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "S" => JoinedStep (τ := τ) (Φ := Φ) pe
local infixr:65 " ⊕ₜ " => Silmaril.coprod

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton (ofRegion_eq_iff)

set_option hygiene false in
local notation "T" => Step (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "H" => fromBinaryFold (τ := τ) (Φ := Φ) pe

/-- On ordinary Paper arrows the two projections compose literally. -/
theorem projection_comp_fromBinaryFold :
    Paper.Extension.Singleton.projection S ⋙ (H) = Paper.Extension.Singleton.projection T :=
  CategoryTheory.Quotient.lift_spec _ _ _

/-- The one extra family gives uniformity for the exact three-copy square. -/
theorem ternary_uniformity {A B : τ} (g : ofType S A ⟶ ofType S B ⨿ ofType S A) :
    (H).map (iterateChosen S (ternaryStep pe g)) =
      (H).map ((inclusion S).map (ternaryFold pe A) ≫ iterateChosen S g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldWithTripling.ternary_uniformity pe g

/-- The added family is already derivable in BinaryFold exactly when all
typed BinaryFold rounds already satisfy tripling. -/
theorem seed_derivable_iff :
    (∀ {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}, TriplingStep pe Γ r s L →
      BinaryFold.Eqv pe Γ r s L) ↔
    (∀ {A B : τ} (g : ofType S A ⟶ ofType S B ⨿ ofType S A),
      iterateChosen S (triple g) = iterateChosen S g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldWithTripling.seed_derivable_iff pe

/-- The written short-circuit three-round arrow has the same iteration as
one round on any retained syntax type in the new quotient. -/
theorem triple_step {A B : τ} (g : ofType T A ⟶ ofType T B ⨿ ofType T A) :
    iterateChosen T (triple g) = iterateChosen T g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldWithTripling.triple_step pe g

/-- Recover the equation on any two guarded representatives at the
original singleton interface. -/
theorem eqv_tripling {A B : τ} {r s : Region Φ} (hr : ValueBranches [A] r [B])
    (hs : ValueBranches [A] s [B]) (g : ofType T A ⟶ ofType T B ⨿ ofType T A)
    (left : ofRegion T hr = iterateChosen T (triple g))
    (right : ofRegion T hs = iterateChosen T g) :
    Eqv pe [A] r s [B] :=
  (ofRegion_eq_iff T hr hs).mp (left.trans ((triple_step pe g).trans right.symm))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling
