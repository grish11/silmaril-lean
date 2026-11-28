module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.KnownTag.Pruning.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.Trim.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.KnownTag

/-! # Exact witnesses for a let followed by a known-tag case -/

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

variable {Γ : VCtx (Ty κ)} {L : LCtx (Ty κ)} {a : Tm Φ} {A : Ty κ}
  {left right : Region Φ}
  {f g : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}

/-- The selected arm may use the case payload and the original environment.
Its renaming skips the bound sum at index 1. The right arm can be any
exactly typed region. The new witness binds the original payload once. -/
theorem RegionDenotes.let_inl_case (determined : TypeDetermined Γ a A)
    {h : Region.HasType Γ (.let₁ (.inl a)
      (.case (.var 0) (left.renameVars (Silmaril.DeBruijn.lift Nat.succ)) right)) L}
    (d : RegionDenotes J M h f) :
    ∃ (ha : a.HasType Γ A) (hb : left.HasType (A :: Γ) L), RegionDenotes J M (.let₁ ha hb) f :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.KnownTag.let_inl_case J M determined d

/-- When the remaining payload term and selected arm have determined
intermediate typing, arbitrary exact witnesses agree. The right arm can
even differ between the two witnesses. -/
theorem RegionDenotes.let_inl_case_eq (determined : TypeDetermined Γ a A)
    (value : DeterminedTerm Γ a A) (selected : DeterminedRegion (A :: Γ) left L)
    {right' : Region Φ}
    {h : Region.HasType Γ (.let₁ (.inl a)
      (.case (.var 0) (left.renameVars (Silmaril.DeBruijn.lift Nat.succ)) right)) L}
    {h' : Region.HasType Γ (.let₁ (.inl a)
      (.case (.var 0) (left.renameVars (Silmaril.DeBruijn.lift Nat.succ)) right')) L}
    (d : RegionDenotes J M h f) (e : RegionDenotes J M h' g) : f = g := by
  obtain ⟨_, _, d'⟩ := d.let_inl_case J M determined
  obtain ⟨_, _, e'⟩ := e.let_inl_case J M determined
  exact (DeterminedRegion.let₁ determined value selected).denotes_eq J M d' e'

/-- The entry normalization preserves the chosen internal family, all block
witnesses, and the actual nonempty CFG dispatch arrow. -/
theorem RegionDenotes.cfg_let_inl_case_entry (determined : TypeDetermined Γ a A)
    {n : Nat} {blocks : Fin (n + 1) → Region Φ}
    {h : Region.HasType Γ (.cfg (.let₁ (.inl a)
      (.case (.var 0) (left.renameVars (Silmaril.DeBruijn.lift Nat.succ)) right)) (n + 1) blocks) L}
    (d : RegionDenotes J M h f) :
    ∃ ht : Region.HasType Γ (.cfg (.let₁ a left) (n + 1) blocks) L, RegionDenotes J M ht f :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.KnownTag.cfg_entry J M determined d

/-- Compare sparse CFG witnesses whose selected entry has the stated
captured-row shape after native known-tag normalization. The shape is
syntactic. The input witnesses supply the actual label families. -/
theorem UnusedSummand.Program.denotes_eq_let_inl_case_entry
    {n : Nat} {P : Fin (n + 1) → Ty κ} {blocks : Fin (n + 1) → Region Φ}
    {tag : Bool} (p : UnusedSummand.Program (Φ := Φ) P L Γ) (roll : IterationRolling C)
    (determined : TypeDetermined Γ a A)
    (shape : p.region tag = .cfg (.let₁ a left) (n + 1) blocks)
    {right' : Region Φ}
    {h : Region.HasType Γ (.cfg (.let₁ (.inl a)
      (.case (.var 0) (left.renameVars (Silmaril.DeBruijn.lift Nat.succ)) right)) (n + 1) blocks) L}
    {h' : Region.HasType Γ (.cfg (.let₁ (.inl a)
      (.case (.var 0) (left.renameVars (Silmaril.DeBruijn.lift Nat.succ)) right')) (n + 1) blocks) L}
    (d : RegionDenotes J M h f) (e : RegionDenotes J M h' g) : f = g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.KnownTag.cfg_agree J M p roll determined shape d e

/-- Restore the constructor on the already-bound payload, then prune the
certified tests. Effectful initializers retained by the certificate run in
their original order. -/
theorem RegionDenotes.let_case_prune (tag : CaseTag) (determined : TypeDetermined Γ a A) {live : Region Φ}
    (steps : Region.PruneConstructorTests ((tag.select left right).substVars (Tm.restoreTag tag)) live)
    {h : Region.HasType Γ (.let₁ (tag.inject a) (.case (.var 0) left right)) L}
    (d : RegionDenotes J M h f) :
    ∃ ht : Region.HasType Γ (.let₁ a live) L, RegionDenotes J M ht f :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.KnownTag.let_case_prune J M tag determined steps d

/-- Compare the original CFG witnesses when the restored old tag can be
pruned to an entry in the trimmed CFG fragment. The syntax certificate
supplies the reduced entry, and the graph supplies the typing and arrows. -/
theorem UnusedSummand.Program.denotes_eq_let_case_prune
    {n : Nat} {P : Fin (n + 1) → Ty κ} {blocks : Fin (n + 1) → Region Φ}
    {renderTag : Bool} (p : UnusedSummand.Program (Φ := Φ) P L Γ) (roll : IterationRolling C) (tag : CaseTag)
    (determined : TypeDetermined Γ a A) {live : Region Φ}
    (steps : Region.PruneConstructorTests ((tag.select left right).substVars (Tm.restoreTag tag)) live)
    (shape : p.region renderTag = .cfg (.let₁ a live) (n + 1) blocks)
    {h : Region.HasType Γ (.cfg (.let₁ (tag.inject a) (.case (.var 0) left right)) (n + 1) blocks) L}
    (d : RegionDenotes J M h f) (e : RegionDenotes J M h g) : f = g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.KnownTag.cfg_prune_agree J M p roll tag
    determined steps shape d e

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
