module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Substitution

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

theorem instantiate_two_retaining_one_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hH : StructuralTheory levels H) {Γ : Ctx}
    {A I a : Tm 0} {B : Tm 1} {t u : Tm 2}
    {L : Finset String} {K : String → Finset String}
    (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels H .unit .star .star)
    (ha : Γ.JEqB levels H A a a)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (ht : ∀ x ∉ L, ∀ y ∉ K x,
      ((Γ.cons x A).cons y (B.open x)).JEqB levels H I
        ((t.open x).open y) ((u.open x).open y)) :
    ∃ N : Finset String, ∀ y ∉ N,
      (Γ.cons y (B.lst a)).JEqB levels H I ((t.lst a).open y) ((u.lst a).open y) := by
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
    (L ∪ Γ.typeFvs ∪ A.fvs ∪ B.fvs ∪ I.fvs ∪ t.fvs ∪ u.fvs ∪ a.fvs)
  simp only [Finset.mem_union, not_or, and_assoc] at hx
  rcases hx with ⟨hxL, hxΓ, hxA, hxB, hxI, hxt, hxu, hxa⟩
  have hBinst : Γ.JEqB levels H (.univ n) (B.lst a) (B.lst a) := by
    simpa only [Tm.lst] using Ctx.JEqB.instantiate_of_hypotheses (B := .univ n) hH.weakening (fun x => hH.substitution x _) hΓ ha
      (by simpa only [Tm.open] using hB)
  refine ⟨K x ∪ insert x (Γ.dv ∪ a.fvs), ?_⟩
  intro y hy
  have hyK : y ∉ K x := fun h => hy (Finset.mem_union_left _ h)
  have hyx : y ≠ x := by
    intro heq
    exact hy (Finset.mem_union_right _ (heq ▸ Finset.mem_insert_self x (Γ.dv ∪ a.fvs)))
  have hyΓ : y ∉ Γ.dv := fun h =>
    hy (Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ h)))
  have hBsubst : (B.open x).fsubst x a = B.lst a := Tm.fsubst_open_self x a B hxB
  have hctx : (Γ.cons y ((B.open x).fsubst x a)).JEqB levels H .unit .star .star := by
    rw [hBsubst]
    exact .cons_ok hn hΓ hyΓ hBinst
  have e₀ : Ctx.SubstB levels x a (Γ.cons x A) Γ H := Ctx.SubstB.drop hΓ ha hxΓ hxA
  have e₁ : Ctx.SubstB levels x a ((Γ.cons x A).cons y (B.open x))
      (Γ.cons y ((B.open x).fsubst x a)) H := Ctx.SubstB.cons_of_hypotheses hH.weakening e₀ hyx hyΓ hctx
  have hresult := (ht x hxL y hyK).substitute_of_hypotheses hH.weakening x a (hH.substitution x a) _ e₁ hctx
  simpa only [hBsubst, Tm.fsubst_fresh x a I hxI, Tm.fsubst_open x a _ hyx,
    Tm.fsubst_open_self x a t hxt, Tm.fsubst_open_self x a u hxu] using hresult

theorem instantiate_two_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hH : StructuralTheory levels H) {Γ : Ctx}
    {A I a b : Tm 0} {B : Tm 1} {t u : Tm 2}
    {L : Finset String} {K : String → Finset String}
    (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels H .unit .star .star)
    (ha : Γ.JEqB levels H A a a) (hb : Γ.JEqB levels H (B.lst a) b b)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (ht : ∀ x ∉ L, ∀ y ∉ K x,
      ((Γ.cons x A).cons y (B.open x)).JEqB levels H I
        ((t.open x).open y) ((u.open x).open y)) :
    Γ.JEqB levels H I ((t.lst a).lst b) ((u.lst a).lst b) := by
  obtain ⟨N, hN⟩ := instantiate_two_retaining_one_of_hypotheses hH hn hΓ ha hB ht
  simpa only [Tm.closed_wk0_lst] using Ctx.JEqB.instantiate_of_hypotheses (B := I.wk0) hH.weakening (fun x => hH.substitution x _) hΓ hb
    (by simpa only [Tm.closed_wk0_open] using hN)

/-- Substitute a first argument while retaining two arbitrary dependent declarations. -/
theorem instantiate_under_two_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hH : StructuralTheory levels H) {Γ : Ctx} {A I a : Tm 0}
    {B : Tm 1} {C : Tm 2} {t u : Tm 3} {L : Finset String}
    (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels H .unit .star .star)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hC : ∀ x ∉ L, ∀ y ∉ insert x L,
      ((Γ.cons x A).cons y (B.open x)).JEqB levels H (.univ n)
        ((C.open x).open y) ((C.open x).open y))
    (ht : ∀ x ∉ L, ∀ y ∉ insert x L, ∀ z ∉ insert y (insert x L),
      (((Γ.cons x A).cons y (B.open x)).cons z ((C.open x).open y)).JEqB levels H I
        (((t.open x).open y).open z) (((u.open x).open y).open z))
    (ha : Γ.JEqB levels H A a a) :
    ∃ N : Finset String, ∀ y ∉ N, ∀ z ∉ insert y N,
      ((Γ.cons y (B.lst a)).cons z ((C.lst a).open y)).JEqB levels H I
        (((t.lst a).open y).open z) (((u.lst a).open y).open z) := by
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
    (L ∪ Γ.dv ∪ Γ.typeFvs ∪ A.fvs ∪ I.fvs ∪ B.fvs ∪ C.fvs ∪ t.fvs ∪ u.fvs ∪ a.fvs)
  have hxParts : x ∉ L ∧ x ∉ Γ.dv ∧ x ∉ Γ.typeFvs ∧ x ∉ A.fvs ∧ x ∉ I.fvs ∧
      x ∉ B.fvs ∧ x ∉ C.fvs ∧ x ∉ t.fvs ∧ x ∉ u.fvs ∧ x ∉ a.fvs := by
    simpa only [Finset.mem_union, not_or, and_assoc] using hx
  rcases hxParts with ⟨hxL, hxΓ, hxT, hxA, hxI, hxB, hxC, hxt, hxu, hxa⟩
  refine ⟨insert x (L ∪ Γ.dv ∪ a.fvs), ?_⟩
  intro y hy z hz
  have hyParts : y ≠ x ∧ y ∉ L ∧ y ∉ Γ.dv ∧ y ∉ a.fvs := by
    simpa only [Finset.mem_insert, Finset.mem_union, not_or, and_assoc] using hy
  have hzParts : z ≠ y ∧ z ≠ x ∧ z ∉ L ∧ z ∉ Γ.dv ∧ z ∉ a.fvs := by
    simpa only [Finset.mem_insert, Finset.mem_union, not_or, and_assoc] using hz
  rcases hyParts with ⟨hyx, hyL, hyΓ, hya⟩
  rcases hzParts with ⟨hzy, hzx, hzL, hzΓ, hza⟩
  have hyS : y ∉ insert x L := by simpa only [Finset.mem_insert, not_or] using And.intro hyx hyL
  have hzS : z ∉ insert y (insert x L) := by
    simpa only [Finset.mem_insert, not_or, and_assoc] using And.intro hzy (And.intro hzx hzL)
  have hBsub : (B.open x).fsubst x a = B.lst a := Tm.fsubst_open_self x a B hxB
  have hCsub : ((C.open x).open y).fsubst x a = (C.lst a).open y := by
    rw [Tm.fsubst_open x a _ hyx, Tm.fsubst_open_self x a C hxC]
  have hBa : Γ.JEqB levels H (.univ n) (B.lst a) (B.lst a) := by
    simpa only [Tm.lst] using Ctx.JEqB.instantiate_of_hypotheses (B := .univ n) hH.weakening (fun x => hH.substitution x _) hΓ ha
      (fun q hq => by simpa only [Tm.open] using hB q hq)
  have hctx : (Γ.cons y ((B.open x).fsubst x a)).JEqB levels H .unit .star .star := by
    rw [hBsub]
    exact .cons_ok hn hΓ hyΓ hBa
  have e : Ctx.SubstB levels x a (Γ.cons x A) Γ H := Ctx.SubstB.drop hΓ ha hxT hxA
  have ey : Ctx.SubstB levels x a ((Γ.cons x A).cons y (B.open x))
      (Γ.cons y ((B.open x).fsubst x a)) H := Ctx.SubstB.cons_of_hypotheses hH.weakening e hyx hyΓ hctx
  have hC' : (Γ.cons y ((B.open x).fsubst x a)).JEqB levels H (.univ n)
      (((C.open x).open y).fsubst x a) (((C.open x).open y).fsubst x a) := by
    simpa only [Tm.fsubst] using (hC x hxL y hyS).substitute_of_hypotheses hH.weakening x a (hH.substitution x a) _ ey hctx
  have hzFresh : z ∉ (Γ.cons y ((B.open x).fsubst x a)).dv := by
    simpa only [Ctx.dv, Finset.mem_insert, not_or] using And.intro hzy hzΓ
  have hctxZ : ((Γ.cons y ((B.open x).fsubst x a)).cons z
      (((C.open x).open y).fsubst x a)).JEqB levels H .unit .star .star :=
    .cons_ok hn hctx hzFresh hC'
  have ez : Ctx.SubstB levels x a
      (((Γ.cons x A).cons y (B.open x)).cons z ((C.open x).open y))
      ((Γ.cons y ((B.open x).fsubst x a)).cons z (((C.open x).open y).fsubst x a)) H :=
    Ctx.SubstB.cons_of_hypotheses hH.weakening ey hzx hzFresh hctxZ
  have hresult := (ht x hxL y hyS z hzS).substitute_of_hypotheses hH.weakening x a (hH.substitution x a) _ ez hctxZ
  simpa only [hBsub, hCsub, Tm.fsubst_fresh x a I hxI,
    Tm.fsubst_open x a _ hzx, Tm.fsubst_open x a _ hyx,
    Tm.fsubst_open_self x a t hxt, Tm.fsubst_open_self x a u hxu] using hresult

/-- Instantiate the first two arguments while retaining the final dependent declaration. -/
theorem instantiate_three_retaining_one_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hH : StructuralTheory levels H) {Γ : Ctx} {A I a b : Tm 0}
    {B : Tm 1} {C : Tm 2} {t u : Tm 3} {L : Finset String}
    (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels H .unit .star .star)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hC : ∀ x ∉ L, ∀ y ∉ insert x L,
      ((Γ.cons x A).cons y (B.open x)).JEqB levels H (.univ n)
        ((C.open x).open y) ((C.open x).open y))
    (ht : ∀ x ∉ L, ∀ y ∉ insert x L, ∀ z ∉ insert y (insert x L),
      (((Γ.cons x A).cons y (B.open x)).cons z ((C.open x).open y)).JEqB levels H I
        (((t.open x).open y).open z) (((u.open x).open y).open z))
    (ha : Γ.JEqB levels H A a a) (hb : Γ.JEqB levels H (B.lst a) b b) :
    ∃ N : Finset String, ∀ z ∉ N,
      (Γ.cons z ((C.lst a).lst b)).JEqB levels H I
        ((((t.lst a).lst b).open z)) ((((u.lst a).lst b).open z)) := by
  obtain ⟨N, hN⟩ := instantiate_under_two_of_hypotheses hH hn hΓ hB hC ht ha
  have hCformed : ∀ x ∉ L, ∀ y ∉ insert x L,
      ((Γ.cons x A).cons y (B.open x)).JEqB levels H (.univ n)
        ((C.open x).open y) ((C.open x).open y) := hC
  obtain ⟨M, hM⟩ := instantiate_two_retaining_one_of_hypotheses hH hn hΓ ha hB hCformed
  apply instantiate_two_retaining_one_of_hypotheses hH (L := M ∪ N) (K := fun y => insert y N) hn hΓ hb
  · intro y hy
    exact hM y (fun h => hy (Finset.mem_union_left _ h))
  · intro y hy z hz
    exact hN y (fun h => hy (Finset.mem_union_right _ h)) z hz

/-- Three actual arguments instantiate arbitrary constant-result telescope judgments. -/
theorem instantiate_three_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hH : StructuralTheory levels H) {Γ : Ctx} {A I a b c : Tm 0}
    {B : Tm 1} {C : Tm 2} {t u : Tm 3} {L : Finset String}
    (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels H .unit .star .star)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hC : ∀ x ∉ L, ∀ y ∉ insert x L,
      ((Γ.cons x A).cons y (B.open x)).JEqB levels H (.univ n)
        ((C.open x).open y) ((C.open x).open y))
    (ht : ∀ x ∉ L, ∀ y ∉ insert x L, ∀ z ∉ insert y (insert x L),
      (((Γ.cons x A).cons y (B.open x)).cons z ((C.open x).open y)).JEqB levels H I
        (((t.open x).open y).open z) (((u.open x).open y).open z))
    (ha : Γ.JEqB levels H A a a) (hb : Γ.JEqB levels H (B.lst a) b b)
    (hc : Γ.JEqB levels H ((C.lst a).lst b) c c) :
    Γ.JEqB levels H I (((t.lst a).lst b).lst c) (((u.lst a).lst b).lst c) := by
  obtain ⟨N, hN⟩ := instantiate_three_retaining_one_of_hypotheses hH hn hΓ hB hC ht ha hb
  simpa only [Tm.closed_wk0_lst] using Ctx.JEqB.instantiate_of_hypotheses (B := I.wk0) hH.weakening (fun x => hH.substitution x _) hΓ hc
    (by simpa only [Tm.closed_wk0_open] using hN)


theorem instantiate_two_retaining_one {levels : RuleBudget} {n : ℕ} {Γ : Ctx}
    {A I a : Tm 0} {B : Tm 1} {t u : Tm 2}
    {L : Finset String} {K : String → Finset String}
    (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (ha : Γ.JEqB levels ∅ A a a)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (ht : ∀ x ∉ L, ∀ y ∉ K x,
      ((Γ.cons x A).cons y (B.open x)).JEqB levels ∅ I
        ((t.open x).open y) ((u.open x).open y)) :
    ∃ N : Finset String, ∀ y ∉ N,
      (Γ.cons y (B.lst a)).JEqB levels ∅ I ((t.lst a).open y) ((u.lst a).open y) :=
  instantiate_two_retaining_one_of_hypotheses (StructuralTheory.empty levels) hn hΓ ha hB ht

theorem instantiate_two {levels : RuleBudget} {n : ℕ} {Γ : Ctx}
    {A I a b : Tm 0} {B : Tm 1} {t u : Tm 2}
    {L : Finset String} {K : String → Finset String}
    (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (ha : Γ.JEqB levels ∅ A a a) (hb : Γ.JEqB levels ∅ (B.lst a) b b)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (ht : ∀ x ∉ L, ∀ y ∉ K x,
      ((Γ.cons x A).cons y (B.open x)).JEqB levels ∅ I
        ((t.open x).open y) ((u.open x).open y)) :
    Γ.JEqB levels ∅ I ((t.lst a).lst b) ((u.lst a).lst b) :=
  instantiate_two_of_hypotheses (StructuralTheory.empty levels) hn hΓ ha hb hB ht

theorem instantiate_under_two {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A I a : Tm 0}
    {B : Tm 1} {C : Tm 2} {t u : Tm 3} {L : Finset String}
    (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (hC : ∀ x ∉ L, ∀ y ∉ insert x L,
      ((Γ.cons x A).cons y (B.open x)).JEqB levels ∅ (.univ n)
        ((C.open x).open y) ((C.open x).open y))
    (ht : ∀ x ∉ L, ∀ y ∉ insert x L, ∀ z ∉ insert y (insert x L),
      (((Γ.cons x A).cons y (B.open x)).cons z ((C.open x).open y)).JEqB levels ∅ I
        (((t.open x).open y).open z) (((u.open x).open y).open z))
    (ha : Γ.JEqB levels ∅ A a a) :
    ∃ N : Finset String, ∀ y ∉ N, ∀ z ∉ insert y N,
      ((Γ.cons y (B.lst a)).cons z ((C.lst a).open y)).JEqB levels ∅ I
        (((t.lst a).open y).open z) (((u.lst a).open y).open z) :=
  instantiate_under_two_of_hypotheses (StructuralTheory.empty levels) hn hΓ hB hC ht ha

theorem instantiate_three_retaining_one {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A I a b : Tm 0}
    {B : Tm 1} {C : Tm 2} {t u : Tm 3} {L : Finset String}
    (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (hC : ∀ x ∉ L, ∀ y ∉ insert x L,
      ((Γ.cons x A).cons y (B.open x)).JEqB levels ∅ (.univ n)
        ((C.open x).open y) ((C.open x).open y))
    (ht : ∀ x ∉ L, ∀ y ∉ insert x L, ∀ z ∉ insert y (insert x L),
      (((Γ.cons x A).cons y (B.open x)).cons z ((C.open x).open y)).JEqB levels ∅ I
        (((t.open x).open y).open z) (((u.open x).open y).open z))
    (ha : Γ.JEqB levels ∅ A a a) (hb : Γ.JEqB levels ∅ (B.lst a) b b) :
    ∃ N : Finset String, ∀ z ∉ N,
      (Γ.cons z ((C.lst a).lst b)).JEqB levels ∅ I
        ((((t.lst a).lst b).open z)) ((((u.lst a).lst b).open z)) :=
  instantiate_three_retaining_one_of_hypotheses (StructuralTheory.empty levels) hn hΓ hB hC ht ha hb

theorem instantiate_three {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A I a b c : Tm 0}
    {B : Tm 1} {C : Tm 2} {t u : Tm 3} {L : Finset String}
    (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (hC : ∀ x ∉ L, ∀ y ∉ insert x L,
      ((Γ.cons x A).cons y (B.open x)).JEqB levels ∅ (.univ n)
        ((C.open x).open y) ((C.open x).open y))
    (ht : ∀ x ∉ L, ∀ y ∉ insert x L, ∀ z ∉ insert y (insert x L),
      (((Γ.cons x A).cons y (B.open x)).cons z ((C.open x).open y)).JEqB levels ∅ I
        (((t.open x).open y).open z) (((u.open x).open y).open z))
    (ha : Γ.JEqB levels ∅ A a a) (hb : Γ.JEqB levels ∅ (B.lst a) b b)
    (hc : Γ.JEqB levels ∅ ((C.lst a).lst b) c c) :
    Γ.JEqB levels ∅ I (((t.lst a).lst b).lst c) (((u.lst a).lst b).lst c) :=
  instantiate_three_of_hypotheses (StructuralTheory.empty levels) hn hΓ hB hC ht ha hb hc

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
