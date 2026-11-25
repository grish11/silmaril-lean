module

public import Silmaril.SSA.Isotope.LambdaSSA.Subtyping.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Subtyping.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Subtyping.Categorical

/-! # Structural denotation and coherence for subtyped λSSA -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA.Subtyping.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical (ctxObj labelObj)

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]

section Term

variable (J : V ⥤ C) [DistributiveFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]
  {Γ : VCtx τ} {t : LambdaSSA.Tm Φ} {A : τ}

/-- The directly defined expression denotation satisfies the structural equations. -/
theorem denote_spec (h : Tm.HasType Γ t A) : Denotes J M h (denote J M h) :=
  denote_spec_proof J M h

/-- The structural equations determine the arrow for a fixed subtyped expression derivation. -/
theorem Denotes.eq_denote {h : Tm.HasType Γ t A}
    {f : J.obj (ctxObj (exactTypeModel M) Γ) ⟶ J.obj (M.obj A)}
    (d : Denotes J M h f) : f = denote J M h :=
  denote_unique_proof J M d

@[simp] theorem denote_sub {B : τ}
    (h : Tm.HasType Γ t A) (d : Silmaril.Isotope.Subty A B) :
    denote J M (.sub h d) = denote J M h ≫ J.map (M.subty d) := rfl

end Term

section Region

variable [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]
  {Γ : VCtx τ} {r : LambdaSSA.Region Φ} {L : LCtx τ}

/-- Every subtyped region derivation has a structural denotation. -/
theorem regionDenotes_exists (h : Region.HasType Γ r L) : ∃ f, RegionDenotes J M h f :=
  regionDenotes_exists_proof J M h

/-- Choose a denotation of a proof-relevant SSA region derivation. -/
noncomputable def denoteRegion (h : Region.HasType Γ r L) :
    J.obj (ctxObj (exactTypeModel M) Γ) ⟶ J.obj (labelObj (exactTypeModel M) L) :=
  (regionDenotes_exists J M h).choose

theorem denoteRegion_spec (h : Region.HasType Γ r L) :
    RegionDenotes J M h (denoteRegion J M h) :=
  (regionDenotes_exists J M h).choose_spec

/-- The structural equations determine an arrow for each fixed subtyped region derivation. -/
theorem RegionDenotes.unique {h : Region.HasType Γ r L}
    {f g : J.obj (ctxObj (exactTypeModel M) Γ) ⟶ J.obj (labelObj (exactTypeModel M) L)}
    (d : RegionDenotes J M h f) (e : RegionDenotes J M h g) : f = g :=
  regionDenotes_unique_proof J M d e

/-- A subtyped derivation fixes all expression coercions and block types. -/
theorem regionTypingCoherent : RegionTypingCoherent (Φ := Φ) J M :=
  ⟨RegionDenotes.unique J M⟩

/-- Under region coherence the structural denotation is the chosen arrow. -/
theorem RegionDenotes.eq_denote [RegionTypingCoherent (Φ := Φ) J M]
    {h : Region.HasType Γ r L}
    {f : J.obj (ctxObj (exactTypeModel M) Γ) ⟶ J.obj (labelObj (exactTypeModel M) L)}
    (d : RegionDenotes J M h f) : f = denoteRegion J M h :=
  RegionTypingCoherent.denotes_eq d (denoteRegion_spec J M h)

end Region

end Silmaril.Isotope.LambdaSSA.Subtyping.Semantics.Categorical
