module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Trim.Check.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Live.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Trim.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Restriction.Check.Thms

/-! # Read an original exact CFG witness through a checked written restriction -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgRestrictionCheck

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

theorem checked {Φ : Type v} {m n exitCount : Nat} {keep : Fin m ↪ Fin n} {r : Region Φ}
    {c : CfgRestriction Φ n} (ok : CfgRestriction.check? keep exitCount r = some c) :
    c.Valid keep exitCount r := by
  cases r <;> try contradiction
  rename_i entry size rows
  simp only [CfgRestriction.check?] at ok
  split at ok <;> try contradiction
  rename_i sizeEq
  subst size
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at ok
  obtain ⟨entry', he, rows', hr, rfl⟩ := ok
  have ent := Region.restrictLabels?_sound he
  have rows := fun i => Region.restrictLabels?_sound (Region.checkFamily_some hr i)
  refine ⟨?_, ent.1, fun i => (rows i).1⟩
  simp only [CfgRestriction.source, ent.2, funext fun i => (rows i).2]

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ]

theorem witnesses {m n : Nat} {keep : Fin (m + 1) ↪ Fin (n + 1)}
    {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ} {c : CfgRestriction Φ (n + 1)}
    (w : c.Valid keep L.length r) (roll : IterationRolling C) {h : r.HasType Γ L}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)} (d : RegionDenotes J M h f) :
    ∃ S : Fin (n + 1) → τ,
      CfgDenotesAt J M S (c.entry.renameLabels (retainLabelIndex keep))
        (fun i => (c.rows i).renameLabels (retainLabelIndex keep)) f ∧
      CfgDenotesAt J M (fun i => S (keep i)) c.entry (fun i => c.rows (keep i)) f := by
  obtain ⟨_, source⟩ : ∃ h' : (c.source keep).HasType Γ L, RegionDenotes J M h' f := by
    rw [w.source]
    exact ⟨h, d⟩
  obtain ⟨S, actual⟩ := source.cfg_readback J M
  exact ⟨S, actual, CfgDenotesAt.restrict J M keep S roll w.entryScope w.rowScope actual⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgRestrictionCheck
