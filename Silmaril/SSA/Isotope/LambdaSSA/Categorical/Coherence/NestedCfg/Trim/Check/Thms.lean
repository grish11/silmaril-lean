module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Trim.Check.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Live.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgRestrictionCheck

/-! # Readback and rolling for a checked restriction of written CFG syntax -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical.CfgRestriction

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

/-- Successful restriction certifies the exact original syntax and bounds. -/
theorem check?_sound {Φ : Type v} {m n exitCount : Nat} {keep : Fin m ↪ Fin n} {r : Region Φ}
    {c : CfgRestriction Φ n} (ok : check? keep exitCount r = some c) : c.Valid keep exitCount r :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgRestrictionCheck.checked ok

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ]

/-- Read the selected family from the original exact witness. The retained
graph uses its actual retained types and has the original arrow. -/
theorem Valid.readback {m n : Nat} {keep : Fin (m + 1) ↪ Fin (n + 1)}
    {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ} {c : CfgRestriction Φ (n + 1)}
    (w : c.Valid keep L.length r) (roll : IterationRolling C) {h : r.HasType Γ L}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)} (d : RegionDenotes J M h f) :
    ∃ S : Fin (n + 1) → τ,
      CfgDenotesAt J M S (c.entry.renameLabels (retainLabelIndex keep))
        (fun i => (c.rows i).renameLabels (retainLabelIndex keep)) f ∧
      CfgDenotesAt J M (fun i => S (keep i)) c.entry (fun i => c.rows (keep i)) f :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgRestrictionCheck.witnesses J M w roll d

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical.CfgRestriction
