module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.Coherence

/-! # Denotation graph uniqueness under determined intermediate typing -/

public section

universe v₁ v₂ u₁ u₂ u v

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.Coherence
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C)
  {κ : Type u} (M : TypeModel (Ty κ) V)
  {Φ : Type v} [HasTy Φ (Ty κ)]

section Term

variable [DistributiveFreydCategory J] [InstructionModel J M Φ]

/-- At a fixed result type, determined intermediate types suffice for uniqueness
of the exact expression graph. -/
theorem DeterminedTerm.denotes_eq {Γ : VCtx (Ty κ)} {a : Tm Φ} {A : Ty κ}
    (rigid : DeterminedTerm Γ a A) {t : Tm.HasType Γ a A}
    {f g : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)}
    (d : Denotes J M t f) (e : Denotes J M t g) : f = g :=
  term_unique J M rigid d e

end Term

section Region

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J] [InstructionModel J M Φ]

/-- The exact region graph is functional for determined syntax, including
nonempty and nested CFGs. -/
theorem DeterminedRegion.denotes_eq {Γ : VCtx (Ty κ)} {r : Region Φ} {L : LCtx (Ty κ)}
    (rigid : DeterminedRegion Γ r L) {t : Region.HasType Γ r L}
    {f g : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
    (d : RegionDenotes J M t f) (e : RegionDenotes J M t g) : f = g :=
  region_unique J M rigid d e

/-- This fragment agrees with the actual selected categorical interpretation. -/
theorem DeterminedRegion.eq_denoteRegion {Γ : VCtx (Ty κ)} {r : Region Φ} {L : LCtx (Ty κ)}
    (rigid : DeterminedRegion Γ r L) {t : Region.HasType Γ r L}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
    (d : RegionDenotes J M t f) : f = denoteRegion J M t :=
  rigid.denotes_eq J M d (denoteRegion_spec J M t)

/-- An entry that branches directly outward runs its argument once. Its graph
witness is independent of the internal block assignments and arrows. -/
theorem RegionDenotes.cfg_outward_branch {Γ : VCtx (Ty κ)} {L : LCtx (Ty κ)} {n i : Nat}
    {a : Tm Φ} {blocks : Fin (n + 1) → Region Φ} {A : Ty κ}
    (exit : At L i A) [FreydCategory.CentralUnit J]
    {t : Region.HasType Γ (.cfg (.br (n + 1 + i) a) (n + 1) blocks) L}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
    (d : RegionDenotes J M t f) :
    ∃ (ta : Tm.HasType Γ a A) (arg : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)),
      Denotes J M ta arg ∧ f = arg ≫ J.map (labelInject M i exit) :=
  cfg_exit J M exit d

/-- The actual chosen arrow of a directly outward CFG equals the chosen arrow
of its bare branch, even for an ambiguous internal label table. -/
theorem denoteRegion_cfg_outward_branch {Γ : VCtx (Ty κ)} {L : LCtx (Ty κ)} {n i : Nat}
    {a : Tm Φ} {blocks : Fin (n + 1) → Region Φ} {A : Ty κ}
    (exit : At L i A) [FreydCategory.CentralUnit J]
    (payload : DeterminedTerm Γ a A) (ha : Tm.HasType Γ a A)
    (t : Region.HasType Γ (.cfg (.br (n + 1 + i) a) (n + 1) blocks) L) :
    denoteRegion J M t = denoteRegion J M (.br exit ha) := by
  obtain ⟨_, _, da, eq⟩ := (denoteRegion_spec J M t).cfg_outward_branch J M exit
  exact eq.trans ((DeterminedRegion.br exit payload).eq_denoteRegion J M (.br da))

end Region

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
