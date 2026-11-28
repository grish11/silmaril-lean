module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.BranchBinding.Comparison.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.Example.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.Example.Thms

/-! # The product-destructuring equation and the raw quotient boundary -/

public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProductDestructureReturns.BranchBinding

open Silmaril CategoryTheory
open CfgEta.TypeCategory (returnRegion returnRegion_typed)
open Paper.RetainedLet (unpackBody unpackBody_typed unpackTerm unpackTerm_typed)
open Paper.Extension.Singleton (ofRegion ofRegion_eq_iff)
open Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding
  (AddBinding eqv_iff_normalized_of_guardedSeed mapSeed)
open Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton
  (RawHom rawClass normalize_guarded)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "ProductJoin" => JoinedStep (τ := τ) (Φ := Φ) pe

/-- Equality in the enlarged raw relation is precisely equality of the
branch-normalized representatives in the enlarged guarded relation. -/
theorem joined_eqv_iff_normalized {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}
    (hr : HasType Γ r L) (hs : HasType Γ s L) :
    Extension.Eqv (AddBinding ProductJoin) Γ r s L ↔
      Extension.Eqv ProductJoin Γ r.bindBranchArguments s.bindBranchArguments L :=
  eqv_iff_normalized_of_guardedSeed joined_valueBranches hr hs

/-- The product-variable fusion itself holds in the enlarged raw relation. -/
theorem raw_unpack {X A D : τ} {b : Tm Φ} (hb : Tm.HasType [A, X] b D) :
    Extension.Eqv (AddBinding ProductJoin) [product X A]
      (unpackBody (returnRegion b)) (returnRegion (unpackTerm b)) [D] :=
  let ⟨hl, hr⟩ := (Step.unpack hb).valueBranches
  .extra hl.hasType hr.hasType (.inl (.inr (.unpack hb)))

/-- Branch binding replays the product-variable fusion in the enlarged guarded join. -/
theorem normalize_unpack {X A D : τ} {b : Tm Φ} (hb : Tm.HasType [A, X] b D) :
    Extension.Eqv ProductJoin [product X A]
      (unpackBody (returnRegion b)).bindBranchArguments
      (returnRegion (unpackTerm b)).bindBranchArguments [D] :=
  let ⟨hl, hr⟩ := (Step.unpack hb).valueBranches
  (joined_eqv_iff_normalized pe hl.hasType hr.hasType).mp (raw_unpack pe hb)

/-- For a guarded representative the change of seed keeps its literal region. -/
theorem normalizeFromOrderedPair_ofRegion {A B : τ} {r : Region Φ}
    (hr : ValueBranches [A] r [B]) :
    (normalizeFromOrderedPair pe).map (X := ⟨A⟩) (Y := ⟨B⟩) (rawClass pe hr.hasType) =
      ofRegion ProductJoin hr :=
  congrArg (orderedPairProjection pe).map (normalize_guarded pe hr)

section Witness

variable {α : Type u} [HasTy Φ (Ty α)]

open Example (U body_typed product_destructure_return_with_branch_binding_fails)

local notation "P" => product (U α) (U α)
local notation "Left" => unpackBody_typed (returnRegion_typed (body_typed (α := α) (Φ := Φ)))
local notation "Right" => returnRegion_typed (unpackTerm_typed (body_typed (α := α) (Φ := Φ)))

/-- The #3680 witness separates the two classes in the actual #3647 raw hom. -/
theorem orderedPair_raw_unpack_ne :
    (rawClass pe (Left).hasType : RawHom (Φ := Φ) pe P P) ≠ rawClass pe (Right).hasType :=
  fun e => product_destructure_return_with_branch_binding_fails pe
    (mapSeed (fun h => h.elim (fun h => .inl (.inl h)) Or.inr) (Quotient.exact e))

/-- At the exact product interface, the old raw-to-guarded comparison followed
by the stronger quotient loses injectivity. -/
theorem normalizeFromOrderedPair_not_injective :
    ¬ Function.Injective ((normalizeFromOrderedPair (τ := Ty α) (Φ := Φ) pe).map
      (X := ⟨P⟩) (Y := ⟨P⟩)) := by
  intro hinj
  apply orderedPair_raw_unpack_ne (α := α) (Φ := Φ) pe
  apply hinj
  rw [normalizeFromOrderedPair_ofRegion pe Left, normalizeFromOrderedPair_ofRegion pe Right]
  exact (ofRegion_eq_iff _ Left Right).mpr (.extra (Left).hasType (Right).hasType (.inr (.unpack body_typed)))

end Witness

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProductDestructureReturns.BranchBinding
