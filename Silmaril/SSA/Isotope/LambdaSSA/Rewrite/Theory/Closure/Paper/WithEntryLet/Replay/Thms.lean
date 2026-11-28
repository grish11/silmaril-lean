module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.SplitImage.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetReplay

/-! # Entry-let seed transport for structural-state squares

`projectSquare_iff` compares the images of the two standard composites.
Native `Paper.Eqv.uniform` requires a derivation between those composites'
region representatives in standard Paper. The seed transport below preserves
corrected equations under the square operations. The split inclusion theorem
uses the corrected square directly.
-/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ Δ : VCtx τ} {L K : LCtx τ} {r s : Region Φ}

/-- Postcomposition by a guarded continuation family sends an entry-let
seed instance to another seed instance. -/
theorem Step.lsubst (h : Step Γ r s L) {σ : Nat → Region Φ}
    (hσ : LSubst.ValueFamily Γ L K σ) : Step Γ (r.lsubst σ) (s.lsubst σ) K :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetReplay.lsubst h hσ

/-- Substitution by constructor values, including precomposition with a
literal constructor state map, preserves the entry-let seed. -/
theorem Step.substVars (h : Step Γ r s L) {θ : Nat → Tm Φ}
    (hθ : ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue Δ (θ i) A) :
    Step Δ (r.substVars θ) (s.substVars θ) L :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetReplay.substVars h hθ

/-- Reindexing the outward labels of both endpoints preserves the seed. -/
theorem Step.renameLabels (h : Step Γ r s L) {ρ : Nat → Nat} (hρ : Ren L K ρ) :
    Step Γ (r.renameLabels ρ) (s.renameLabels ρ) K :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetReplay.renameLabels h hρ

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet
