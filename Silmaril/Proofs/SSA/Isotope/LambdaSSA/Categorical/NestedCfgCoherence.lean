module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms

/-! # Compose the exact graphs of a native CFG -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgCoherence

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Semantics.Categorical

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

variable {Γ : VCtx (Ty κ)} {L : LCtx (Ty κ)} {n : Nat}
  {entry : Region Φ} {blocks : Fin (n + 1) → Region Φ} {R : Fin (n + 1) → Ty κ}
  {f g : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}

theorem readback (labels : LabelsDetermined Γ L entry blocks R)
    {t : (.cfg entry (n + 1) blocks : Region Φ).HasType Γ L} (d : RegionDenotes J M t f) :
    CfgDenotesAt J M R entry blocks f := by
  obtain ⟨S, selected⟩ := d.cfg_readback J M
  have eq : S = R := by
    obtain ⟨he, hb, _⟩ := selected
    exact labels S he hb
  exact eq ▸ selected

theorem compare (entryUnique : RegionDenotes.Functional J M Γ entry (List.ofFn R ++ L))
    (blocksUnique : ∀ i, RegionDenotes.Functional J M (R i :: Γ) (blocks i) (List.ofFn R ++ L))
    (left : CfgDenotesAt J M R entry blocks f) (right : CfgDenotesAt J M R entry blocks g) : f = g := by
  obtain ⟨_, _, fe, _, fc, de, db, dc, rfl⟩ := left
  obtain ⟨_, _, ge, _, gc, ee, eb, ec, rfl⟩ := right
  have entry_eq : fe = ge := entryUnique de ee
  have collective_eq : fc = gc := collective_ext J M n Γ R fun i =>
    (dc.restrict i).trans ((blocksUnique i (db i) (eb i)).trans (ec.restrict i).symm)
  rw [entry_eq, collective_eq]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgCoherence
