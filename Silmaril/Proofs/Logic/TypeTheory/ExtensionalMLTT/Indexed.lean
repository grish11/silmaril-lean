module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Indexed.Defs

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Indexed

open W WEncoding.Terms

/-- Actual proof compilation, preserving the fixed stage and consuming each
source premise recursively before invoking its proved W/equality rule. -/
theorem Derivation.compile {levels : ℕ} {j : Judgment} (d : Derivation levels j) :
    Ctx.JEqB levels ∅ j.encode.Γ j.encode.A j.encode.a j.encode.b := by
  induction d with
  | ordinary d => exact d
  | expose _ ih => exact ih
  | family D _ ih => exact fibre_formation D ih
  | node D _ _ _ hi ha hf => exact node_typing D hi ha hf
  | eliminate D hm _ _ _ _ hC hs hi ht => exact indexedInduction_typing D hm hC hs hi ht
  | compute D hm _ _ _ _ _ hC hs hi ha hf => exact indexedInduction_node_beta D hm hC hs hi ha hf

/-- Source rules remain at the same object levels when their common cap increases. -/
theorem Derivation.include {levels more : ℕ} (h : levels ≤ more) {j : Judgment}
    (d : Derivation levels j) : Derivation more j := by
  induction d with
  | ordinary d => exact .ordinary (d.include h)
  | expose _ ih => exact .expose ih
  | family D _ ih => exact .family (D.includeLevels h) ih
  | node D _ _ _ hi ha hf => exact .node (D.includeLevels h) hi ha hf
  | eliminate D hm _ _ _ _ hC hs hi ht => exact .eliminate (D.includeLevels h) (hm.trans_le h) hC hs hi ht
  | compute D hm _ _ _ _ _ hC hs hi ha hf => exact .compute (D.includeLevels h) (hm.trans_le h) hC hs hi ha hf

/-- Compiling an ordinary judgment adds no syntax. -/
@[simp] theorem Judgment.encode_ordinary (j : W.Jdg) : (Judgment.ordinary j).encode = j := rfl

/-- The annotation-aware source bound controls the entire compiled judgment. -/
theorem Judgment.encode_usesBelow {levels : ℕ} {j : Judgment} (hj : j.UsesBelow levels) :
    j.encode.UsesBelow levels := (Nat.le_max_left _ _).trans hj

/-- All source consequence constructors preserve exact encoded theory leaves. -/
theorem Consequence.compile {levels : ℕ} {H : Set Judgment} {j : Judgment}
    (d : Consequence levels H j) :
    Ctx.JEqB levels (Judgment.encode '' H) j.encode.Γ j.encode.A j.encode.a j.encode.b := by
  cases d with
  | hyp hj => exact .hyp ⟨_, hj, rfl⟩
  | ordinary d => exact d
  | indexed d => exact d.compile.mono (Set.empty_subset _)

/-- Substitute source consequences for source hypotheses. -/
theorem Consequence.bind {levels : ℕ} {H H' : Set Judgment}
    (f : ∀ j ∈ H, Consequence levels H' j) {j : Judgment}
    (d : Consequence levels H j) : Consequence levels H' j := by
  cases d with
  | hyp hj => exact f _ hj
  | ordinary d =>
      apply Consequence.ordinary
      apply d.bind
      rintro q ⟨p, hp, rfl⟩
      exact (f p hp).compile
  | indexed d => exact .indexed d

/-- Enlarging source hypotheses preserves consequence. -/
theorem Consequence.mono {levels : ℕ} {H H' : Set Judgment} (h : H ⊆ H')
    {j : Judgment} (d : Consequence levels H j) : Consequence levels H' j :=
  d.bind fun _ hj => .hyp (h hj)

/-- Increasing the count preserves all source theory leaves and inference steps. -/
theorem Consequence.include {levels more : ℕ} (h : levels ≤ more) {H : Set Judgment}
    {j : Judgment} (d : Consequence levels H j) : Consequence more H j := by
  cases d with
  | hyp hj => exact .hyp hj
  | ordinary d => exact .ordinary (d.include h)
  | indexed d => exact .indexed (d.include h)

/-- The derived-rule extension is conservative on the ordinary W language. -/
theorem Consequence.ordinary_iff {levels : ℕ} {H : Set W.Jdg} {j : W.Jdg} :
    Consequence levels (Judgment.ordinary '' H) (.ordinary j) ↔
      Ctx.JEqB levels H j.Γ j.A j.a j.b := by
  constructor
  · intro d
    simpa [Set.image_image] using d.compile
  · intro d
    apply Consequence.ordinary
    simpa [Set.image_image] using d

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Indexed
