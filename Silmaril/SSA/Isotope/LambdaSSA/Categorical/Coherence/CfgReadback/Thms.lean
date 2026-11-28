module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.CfgReadback

/-! # Inversion and assembly of exact nonempty CFG witnesses -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.CfgReadback
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

/-- Invert a nonempty CFG graph witness into its actual entry, block family,
collective arrow and contextual iterate equation. -/
theorem RegionDenotes.cfg_readback {t : Region.HasType Γ (.cfg entry (n + 1) blocks) L}
    (d : RegionDenotes J M t f) :
    ∃ R : Fin (n + 1) → τ, CfgDenotesAt J M R entry blocks f :=
  readback J M d

/-- Assemble the underlying graph witness from its fixed-family coordinates. -/
theorem CfgDenotesAt.denotes {R : Fin (n + 1) → τ} {t : Region.HasType Γ (.cfg entry (n + 1) blocks) L}
    (d : CfgDenotesAt J M R entry blocks f) : RegionDenotes J M t f :=
  assemble J M d

/-- Construct a graph witness at a specified internal label family. -/
theorem CfgDenotesAt.exists_of_typing (R : Fin (n + 1) → τ)
    (he : Region.HasType Γ entry (List.ofFn R ++ L))
    (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    ∃ f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L), CfgDenotesAt J M R entry blocks f :=
  exists_at J M R he hb

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
