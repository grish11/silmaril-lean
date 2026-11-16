module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Mutual.Defs

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Mutual

open W WEncoding.Terms

universe u

private theorem nilLookupLE (Γ : Ctx) : Ctx.nil.LookupLE Γ := by
  intro x A h
  cases h

/-- Local source index typing compiles to an actual tagged Sigma index. -/
theorem FormationData.taggedIndex_typing {count levels n : ℕ} {M : Description count} {Γ : Ctx}
    (D : FormationData M levels n Γ) (tag : Fin count) {i : Tm 0}
    (hi : Γ.JEqB levels ∅ (M.localType tag) i i) :
    Γ.JEqB levels ∅ M.flatten.index (M.taggedIndex tag i) (M.taggedIndex tag i) := by
  have hlevels : 1 ≤ levels := by have := D.bound; omega
  have htag : Γ.JEqB levels ∅ (.univ 0) (Tags.Tag count) (Tags.Tag count) :=
    ((Encoding.Object.FiniteTag.formation count .nil_ok).include hlevels).weaken
      (nilLookupLE Γ) D.context
  have hvalue : Γ.JEqB levels ∅ (Tags.Tag count) (Tags.canonical tag) (Tags.canonical tag) :=
    ((Encoding.Object.FiniteTag.canonical_typing tag .nil_ok).include hlevels).weaken
      (nilLookupLE Γ) D.context
  exact .pair (n := n) (L := D.names) (by have := D.bound; omega)
    (.cumul (by have := D.bound; omega) (Nat.zero_le n) htag) D.localIndex hvalue hi

/-- Compile every simultaneous source rule into the proved indexed source rules. -/
theorem Derivation.compileIndexed {levels : ℕ} {j : Judgment} (d : Derivation levels j) :
    Indexed.Derivation levels j.toIndexed := by
  induction d with
  | ordinary d => exact .ordinary d
  | expose _ ih => exact .expose ih
  | family D _ hi =>
      exact .family D.toIndexedFormationData (.ordinary (D.taggedIndex_typing _ hi.compile))
  | node D _ _ _ hi ha hf =>
      exact .node D.toIndexedFormationData (.ordinary (D.taggedIndex_typing _ hi.compile)) ha hf
  | eliminate D hm _ _ _ _ hC hs hi ht =>
      exact .eliminate D.toIndexedFormationData hm hC hs
        (.ordinary (D.taggedIndex_typing _ hi.compile)) ht
  | compute D hm _ _ _ _ _ hC hs hi ha hf =>
      exact .compute D.toIndexedFormationData hm hC hs
        (.ordinary (D.taggedIndex_typing _ hi.compile)) ha hf

theorem Derivation.compile {levels : ℕ} {j : Judgment} (d : Derivation levels j) :
    Ctx.JEqB levels ∅ j.encode.Γ j.encode.A j.encode.a j.encode.b := d.compileIndexed.compile

theorem Derivation.include {levels more : ℕ} (h : levels ≤ more) {j : Judgment}
    (d : Derivation levels j) : Derivation more j := by
  induction d with
  | ordinary d => exact .ordinary (d.include h)
  | expose _ ih => exact .expose ih
  | family D _ hi => exact .family (D.includeLevels h) hi
  | node D _ _ _ hi ha hf => exact .node (D.includeLevels h) hi ha hf
  | eliminate D hm _ _ _ _ hC hs hi ht =>
      exact .eliminate (D.includeLevels h) (hm.trans_le h) hC hs hi ht
  | compute D hm _ _ _ _ _ hC hs hi ha hf =>
      exact .compute (D.includeLevels h) (hm.trans_le h) hC hs hi ha hf

@[simp] theorem Judgment.toIndexed_ordinary (j : W.Jdg) :
    (Judgment.ordinary j).toIndexed = .ordinary j := rfl

@[simp] theorem Judgment.encode_ordinary (j : W.Jdg) :
    (Judgment.ordinary j).encode = j := rfl

theorem Judgment.toIndexed_usesBelow {levels : ℕ} {j : Judgment} (hj : j.UsesBelow levels) :
    j.toIndexed.UsesBelow levels := (Nat.le_max_left _ _).trans hj

theorem Judgment.encode_usesBelow {levels : ℕ} {j : Judgment} (hj : j.UsesBelow levels) :
    j.encode.UsesBelow levels := j.toIndexed.encode_usesBelow (j.toIndexed_usesBelow hj)

/-- Compilation preserves the exact images of arbitrary source theory leaves. -/
theorem Consequence.compileIndexed {levels : ℕ} {H : Set Judgment} {j : Judgment}
    (d : Consequence levels H j) :
    Indexed.Consequence levels (Judgment.toIndexed '' H) j.toIndexed := by
  cases d with
  | hyp hj => exact .hyp ⟨_, hj, rfl⟩
  | ordinary d =>
      apply Indexed.Consequence.ordinary
      rw [Set.image_image]
      exact d
  | derived d => exact .indexed d.compileIndexed

theorem Consequence.compile {levels : ℕ} {H : Set Judgment} {j : Judgment}
    (d : Consequence levels H j) :
    Ctx.JEqB levels (Judgment.encode '' H) j.encode.Γ j.encode.A j.encode.a j.encode.b := by
  have h := d.compileIndexed.compile
  rw [Set.image_image] at h
  exact h

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
  | derived d => exact .derived d

theorem Consequence.mono {levels : ℕ} {H H' : Set Judgment} (h : H ⊆ H')
    {j : Judgment} (d : Consequence levels H j) : Consequence levels H' j :=
  d.bind fun _ hj => .hyp (h hj)

theorem Consequence.include {levels more : ℕ} (h : levels ≤ more) {H : Set Judgment}
    {j : Judgment} (d : Consequence levels H j) : Consequence more H j := by
  cases d with
  | hyp hj => exact .hyp hj
  | ordinary d => exact .ordinary (d.include h)
  | derived d => exact .derived (d.include h)

theorem Consequence.ordinary_iff {levels : ℕ} {H : Set W.Jdg} {j : W.Jdg} :
    Consequence levels (Judgment.ordinary '' H) (.ordinary j) ↔
      Ctx.JEqB levels H j.Γ j.A j.a j.b := by
  constructor
  · intro d
    simpa [Set.image_image] using d.compile
  · intro d
    apply Consequence.ordinary
    simpa [Set.image_image] using d

/-- Actual interpreted total indices contain exactly finitely tagged local indices. -/
theorem Description.mem_index_denoteIn_iff {count : ℕ} (M : Description count)
    (U : ℕ → ZFSet.{u}) (ρ : String → ZFSet.{u}) (p : ZFSet.{u}) :
    p ∈ M.flatten.index.denoteIn U ρ Fin.elim0 ↔
      ∃ tag : Fin count, ∃ i : ZFSet.{u},
        i ∈ M.localIndex.denoteIn U ρ
          (Fin.cons (SetSem.pair (Silmaril.Logic.SetTheory.numeral tag.val) ∅) Fin.elim0) ∧
        p = SetSem.pair (SetSem.pair (Silmaril.Logic.SetTheory.numeral tag.val) ∅) i := by
  change p ∈ SetSem.sigma _ _ ↔ _
  rw [SetSem.mem_sigma]
  constructor
  · rintro ⟨t, ht, i, hi, hp⟩
    obtain ⟨tag, rfl⟩ := (Encoding.Object.FiniteTag.mem_denoteIn_iff count U ρ t).1 ht
    exact ⟨tag, i, hi, hp.symm⟩
  · rintro ⟨tag, i, hi, rfl⟩
    exact ⟨_, (Encoding.Object.FiniteTag.mem_denoteIn_iff count U ρ _).2 ⟨tag, rfl⟩, i, hi, rfl⟩

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Mutual
