module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical

/-! # Existence and conditional coherence of categorical λSSA denotation -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]

section Collective

variable (J : Functor V C) [DistributiveFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)

/-- In a nonempty block family, an arrow out of the context and internal
label coproduct is determined by its restriction to each block. -/
theorem collective_ext (n : Nat) (Γ : VCtx τ) (R : Fin (n + 1) → τ)
    {Y : C} {f g : J.obj (ctxObj M Γ ⊗ finiteLabelObj M R) ⟶ Y}
    (h : ∀ i, J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteLabelInject M R i) ≫ f =
      J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteLabelInject M R i) ≫ g) :
    f = g :=
  collective_ext_proof J M n Γ R h

end Collective

section Term

variable (J : Functor V C) [DistributiveFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]
  {Γ : VCtx τ} {t : Tm Φ} {A : τ}

/-- Every exactly typed expression has a structural denotation. -/
theorem denotes_exists (h : Tm.HasType Γ t A) : ∃ f, Denotes J M h f :=
  denotes_exists_proof J M h

/-- Choose a denotation of an exactly typed expression. -/
noncomputable def denote (h : Tm.HasType Γ t A) :
    J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A) :=
  (denotes_exists J M h).choose

theorem denote_spec (h : Tm.HasType Γ t A) : Denotes J M h (denote J M h) :=
  (denotes_exists J M h).choose_spec

/-- In a coherent model the denotation graph singles out the chosen arrow. -/
theorem Denotes.eq_denote [TypingCoherent (Φ := Φ) J M]
    {h : Tm.HasType Γ t A} {f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)}
    (d : Denotes J M h f) : f = denote J M h :=
  TypingCoherent.denotes_eq d (denote_spec J M h)

end Term

section Region

variable [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]
  {Γ : VCtx τ} {r : Region Φ} {L : LCtx τ}

/-- A nonempty family of typed blocks has an arrow that restricts to each
block along the corresponding local label injection. -/
theorem collectiveDenotes_exists_succ (n : Nat) (Γ : VCtx τ)
    (R : Fin (n + 1) → τ) (L : LCtx τ)
    (block : ∀ i, J.obj (ctxObj M (R i :: Γ)) ⟶
      J.obj (labelObj M (List.ofFn R ++ L))) :
    ∃ f, CollectiveDenotes J M Γ R L block f :=
  collectiveDenotes_exists_succ_proof J M n Γ R L block

/-- Every exactly typed region has a structural denotation, including nested CFGs. -/
theorem regionDenotes_exists (h : Region.HasType Γ r L) : ∃ f, RegionDenotes J M h f :=
  regionDenotes_exists_proof J M h

/-- Choose a denotation of an exactly typed SSA region. -/
noncomputable def denoteRegion (h : Region.HasType Γ r L) :
    J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L) :=
  (regionDenotes_exists J M h).choose

theorem denoteRegion_spec (h : Region.HasType Γ r L) :
    RegionDenotes J M h (denoteRegion J M h) :=
  (regionDenotes_exists J M h).choose_spec

/-- In a coherent model the region denotation graph singles out the chosen arrow. -/
theorem RegionDenotes.eq_denote [RegionTypingCoherent (Φ := Φ) J M]
    {h : Region.HasType Γ r L} {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
    (d : RegionDenotes J M h f) : f = denoteRegion J M h :=
  RegionTypingCoherent.denotes_eq d (denoteRegion_spec J M h)

end Region

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
