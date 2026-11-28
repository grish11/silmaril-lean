module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms

/-! # Inversion and assembly of exact nonempty CFG witnesses -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.CfgReadback

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ]

variable {Γ : VCtx τ} {L : LCtx τ} {n : Nat}
  {entry : Region Φ} {blocks : Fin (n + 1) → Region Φ}
  {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}

theorem readback {t : Region.HasType Γ (.cfg entry (n + 1) blocks) L}
    (d : RegionDenotes J M t f) :
    ∃ R : Fin (n + 1) → τ, CfgDenotesAt J M R entry blocks f := by
  cases d with
  | cfg he hb de db dc => exact ⟨_, he, hb, _, _, _, de, db, dc, rfl⟩

theorem assemble {R : Fin (n + 1) → τ} {t : Region.HasType Γ (.cfg entry (n + 1) blocks) L}
    (d : CfgDenotesAt J M R entry blocks f) : RegionDenotes J M t f := by
  obtain ⟨he, hb, _, _, _, de, db, dc, rfl⟩ := d
  exact .cfg he hb de db dc

theorem exists_at (R : Fin (n + 1) → τ)
    (he : Region.HasType Γ entry (List.ofFn R ++ L))
    (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    ∃ f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L), CfgDenotesAt J M R entry blocks f := by
  obtain ⟨c, dc⟩ := collectiveDenotes_exists_succ J M n Γ R L (fun i => denoteRegion J M (hb i))
  exact ⟨cfgDispatchArrow J M R (denoteRegion J M he) c, he, hb, _, _, c,
    denoteRegion_spec J M he, fun i => denoteRegion_spec J M (hb i), dc, rfl⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.CfgReadback
