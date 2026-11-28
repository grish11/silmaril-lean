module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgCoherence

/-! # Recursive exact-witness agreement at native CFG boundaries -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {κ : Type u} (M : TypeModel (Ty κ) V) {Φ : Type v} [HasTy Φ (Ty κ)] [InstructionModel J M Φ]

open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgCoherence

/-- Determined syntax supplies local graph functionality. -/
theorem DeterminedRegion.functional {Γ : VCtx (Ty κ)} {L : LCtx (Ty κ)} {r : Region Φ}
    (rigid : DeterminedRegion Γ r L) : RegionDenotes.Functional J M Γ r L :=
  fun {_ _ _ _} d e => rigid.denotes_eq J M d e

variable {Γ : VCtx (Ty κ)} {L : LCtx (Ty κ)} {n : Nat}
  {entry : Region Φ} {blocks : Fin (n + 1) → Region Φ} {R : Fin (n + 1) → Ty κ}
  {f g : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}

/-- Recover the actual entry, row and collective arrows at the family
forced by exact typing. This readback acts on the given graph witness. -/
theorem RegionDenotes.cfg_readback_of_labels_determined (labels : LabelsDetermined Γ L entry blocks R)
    {t : (.cfg entry (n + 1) blocks : Region Φ).HasType Γ L} (d : RegionDenotes J M t f) :
    CfgDenotesAt J M R entry blocks f :=
  readback J M labels d

/-- At a shared internal family, entry and row agreement determine the
original dispatch arrow by the contextual block injections. -/
theorem CfgDenotesAt.eq_of_components
    (entryUnique : RegionDenotes.Functional J M Γ entry (List.ofFn R ++ L))
    (blocksUnique : ∀ i, RegionDenotes.Functional J M (R i :: Γ) (blocks i) (List.ofFn R ++ L))
    (left : CfgDenotesAt J M R entry blocks f) (right : CfgDenotesAt J M R entry blocks g) : f = g :=
  compare J M entryUnique blocksUnique left right

/-- Compose local functionality across a native nonempty CFG. A nested row
receives the block parameter and all older captures. Its outward labels
are the outer local labels followed by the outer exits, in that order.
The inner row may establish functionality with its own varying label
families. Each graph retains its native iteration. -/
theorem RegionDenotes.Functional.cfg (labels : LabelsDetermined Γ L entry blocks R)
    (entryUnique : RegionDenotes.Functional J M Γ entry (List.ofFn R ++ L))
    (blocksUnique : ∀ i, RegionDenotes.Functional J M (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    RegionDenotes.Functional J M Γ (.cfg entry (n + 1) blocks) L :=
  fun {_ _ _ _} d e => CfgDenotesAt.eq_of_components J M entryUnique blocksUnique
    (d.cfg_readback_of_labels_determined J M labels) (e.cfg_readback_of_labels_determined J M labels)

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
