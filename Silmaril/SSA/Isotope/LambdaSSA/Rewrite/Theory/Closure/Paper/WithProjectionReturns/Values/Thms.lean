module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturns.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Constructors.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithProjectionReturnValues

/-! # Both projection values in a common quotient containing the two steps -/

public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturns

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (productFstBranches productSndBranches)
open Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
  (ProjectedCopyingReturn ProjectedCopyingValueCategory ofRegion ofType)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
  (includeStep : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}, Step Γ r s L → Seed Γ r s L)

include includeStep in
/-- The first guarded projection admits a typed pure-return witness and a central copying lift. -/
theorem fst_mem (A B : τ) :
    ProjectedCopyingReturn Seed pe (ofRegion Seed (productFstBranches (Φ := Φ) A B)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithProjectionReturnValues.fst_mem pe Seed includeStep A B

include includeStep in
/-- The second guarded projection admits a typed pure-return witness and a central copying lift. -/
theorem snd_mem (A B : τ) :
    ProjectedCopyingReturn Seed pe (ofRegion Seed (productSndBranches (Φ := Φ) A B)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithProjectionReturnValues.snd_mem pe Seed includeStep A B

set_option hygiene false in
local notation "Values" => ProjectedCopyingValueCategory Seed pe

/-- The two guarded projections form a binary fan in the projected value category. -/
@[expose] def productFan (A B : τ) :
    BinaryFan (⟨ofType Seed A⟩ : Values) (⟨ofType Seed B⟩ : Values) :=
  BinaryFan.mk (P := (⟨ofType Seed (product A B)⟩ : Values))
    ⟨ofRegion Seed (productFstBranches A B), fst_mem pe Seed includeStep A B⟩
    ⟨ofRegion Seed (productSndBranches A B), snd_mem pe Seed includeStep A B⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturns
