module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Instantiation
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Telescope

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

theorem instantiate_two_retaining_one_dependent_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hH : StructuralTheory levels H) {Γ : Ctx}
    {A a : Tm 0} {B : Tm 1} {D t u : Tm 2}
    {L : Finset String} {N : String → Finset String}
    (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels H .unit .star .star)
    (ha : Γ.JEqB levels H A a a)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (ht : ∀ x ∉ L, ∀ y ∉ N x,
      ((Γ.cons x A).cons y (B.open x)).JEqB levels H
        ((D.open x).open y) ((t.open x).open y) ((u.open x).open y)) :
    ∃ M : Finset String, ∀ y ∉ M,
      (Γ.cons y (B.lst a)).JEqB levels H
        ((D.lst a).open y) ((t.lst a).open y) ((u.lst a).open y) := by
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
    (L ∪ Γ.typeFvs ∪ A.fvs ∪ B.fvs ∪ D.fvs ∪ t.fvs ∪ u.fvs ∪ a.fvs)
  simp only [Finset.mem_union, not_or, and_assoc] at hx
  rcases hx with ⟨hxL, hxΓ, hxA, hxB, hxD, hxt, hxu, hxa⟩
  have hBinst : Γ.JEqB levels H (.univ n) (B.lst a) (B.lst a) := by
    simpa only [Tm.lst] using Ctx.JEqB.instantiate_of_hypotheses hH.weakening (fun x => hH.substitution x _) (B := .univ n) hΓ ha
      (by simpa only [Tm.open] using hB)
  refine ⟨N x ∪ insert x (Γ.dv ∪ a.fvs), ?_⟩
  intro y hy
  have hyN : y ∉ N x := fun h => hy (Finset.mem_union_left _ h)
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
  have hresult := (ht x hxL y hyN).substitute_of_hypotheses hH.weakening x a (hH.substitution x a) _ e₁ hctx
  simpa only [hBsubst, Tm.fsubst_open x a _ hyx,
    Tm.fsubst_open_self x a D hxD, Tm.fsubst_open_self x a t hxt,
    Tm.fsubst_open_self x a u hxu] using hresult

theorem instantiate_under_two_dependent_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hH : StructuralTheory levels H) {Γ : Ctx} {A a : Tm 0}
    {B : Tm 1} {C : Tm 2} {D t u : Tm 3} {L : Finset String}
    (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels H .unit .star .star)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hC : ∀ x ∉ L, ∀ y ∉ insert x L,
      ((Γ.cons x A).cons y (B.open x)).JEqB levels H (.univ n)
        ((C.open x).open y) ((C.open x).open y))
    (ht : ∀ x ∉ L, ∀ y ∉ insert x L, ∀ z ∉ insert y (insert x L),
      (((Γ.cons x A).cons y (B.open x)).cons z ((C.open x).open y)).JEqB levels H
        (((D.open x).open y).open z) (((t.open x).open y).open z) (((u.open x).open y).open z))
    (ha : Γ.JEqB levels H A a a) :
    ∃ N : Finset String, ∀ y ∉ N, ∀ z ∉ insert y N,
      ((Γ.cons y (B.lst a)).cons z ((C.lst a).open y)).JEqB levels H
        (((D.lst a).open y).open z) (((t.lst a).open y).open z) (((u.lst a).open y).open z) := by
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
    (L ∪ Γ.dv ∪ Γ.typeFvs ∪ A.fvs ∪ D.fvs ∪ B.fvs ∪ C.fvs ∪ t.fvs ∪ u.fvs ∪ a.fvs)
  have hxParts : x ∉ L ∧ x ∉ Γ.dv ∧ x ∉ Γ.typeFvs ∧ x ∉ A.fvs ∧ x ∉ D.fvs ∧
      x ∉ B.fvs ∧ x ∉ C.fvs ∧ x ∉ t.fvs ∧ x ∉ u.fvs ∧ x ∉ a.fvs := by
    simpa only [Finset.mem_union, not_or, and_assoc] using hx
  rcases hxParts with ⟨hxL, hxΓ, hxT, hxA, hxD, hxB, hxC, hxt, hxu, hxa⟩
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
    simpa only [Tm.lst] using Ctx.JEqB.instantiate_of_hypotheses hH.weakening (fun x => hH.substitution x _) (B := .univ n) hΓ ha
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
  simpa only [hBsub, hCsub,
    Tm.fsubst_open x a _ hzx, Tm.fsubst_open x a _ hyx,
    Tm.fsubst_open_self x a D hxD, Tm.fsubst_open_self x a t hxt,
    Tm.fsubst_open_self x a u hxu] using hresult

theorem doubleAbstraction_beta_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hH : StructuralTheory levels H) {Γ : Ctx}
    {A a b : Tm 0} {B : Tm 1} {D K : Tm 2} {L : Finset String}
    (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hD : ∀ x ∉ L, ∀ y ∉ insert x L,
      ((Γ.cons x A).cons y (B.open x)).JEqB levels H (.univ n)
        ((D.open x).open y) ((D.open x).open y))
    (hK : ∀ x ∉ L, ∀ y ∉ insert x L,
      ((Γ.cons x A).cons y (B.open x)).JEqB levels H
        ((D.open x).open y) ((K.open x).open y) ((K.open x).open y))
    (ha : Γ.JEqB levels H A a a) (hb : Γ.JEqB levels H (B.lst a) b b) :
    Γ.JEqB levels H ((D.lst a).lst b)
      (.app (.app (.abs A (.abs B K)) a) b) ((K.lst a).lst b) := by
  have hTail : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n)
      ((.pi B D : Tm 1).open x) ((.pi B D : Tm 1).open x) := by
    intro x hx
    simpa only [Tm.open] using Ctx.JEqB.pi hn (hB x hx) (hD x hx)
  have hInner : ∀ x ∉ L, (Γ.cons x A).JEqB levels H ((.pi B D : Tm 1).open x)
      ((.abs B K : Tm 1).open x) ((.abs B K : Tm 1).open x) := by
    intro x hx
    simpa only [Tm.open] using Ctx.JEqB.abs hn (hB x hx) (hD x hx) (hK x hx)
  have hFirst := Ctx.JEqB.beta_app hn hA hTail hInner ha
  simp only [Tm.lst] at hFirst
  have hBa : Γ.JEqB levels H (.univ n) (B.lst a) (B.lst a) := by
    simpa only [Tm.lst] using Ctx.JEqB.instantiate_of_hypotheses hH.weakening (fun x => hH.substitution x _) (B := .univ n) hΓ ha
      (by simpa only [Tm.open] using hB)
  obtain ⟨N, hDa⟩ := Ctx.JEqB.instantiate_two_retaining_one_of_hypotheses hH hn hΓ ha hB hD
  obtain ⟨M, hKa⟩ := instantiate_two_retaining_one_dependent_of_hypotheses hH hn hΓ ha hB hK
  have hDa' : ∀ y ∉ N ∪ M, (Γ.cons y (B.lst a)).JEqB levels H (.univ n)
      ((D.lst a).open y) ((D.lst a).open y) := by
    intro y hy
    exact hDa y (fun h => hy (Finset.mem_union_left _ h))
  have hKa' : ∀ y ∉ N ∪ M, (Γ.cons y (B.lst a)).JEqB levels H ((D.lst a).open y)
      ((K.lst a).open y) ((K.lst a).open y) := by
    intro y hy
    exact hKa y (fun h => hy (Finset.mem_union_right _ h))
  exact (Ctx.JEqB.app hn hBa hDa' hFirst hb).trans (Ctx.JEqB.beta_app hn hBa hDa' hKa' hb)

theorem tripleAbstraction_beta_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hH : StructuralTheory levels H) {Γ : Ctx}
    {A a b c : Tm 0} {B : Tm 1} {C : Tm 2} {D K : Tm 3} {L : Finset String}
    (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hC : ∀ x ∉ L, ∀ f ∉ insert x L,
      ((Γ.cons x A).cons f (B.open x)).JEqB levels H (.univ n)
        ((C.open x).open f) ((C.open x).open f))
    (hD : ∀ x ∉ L, ∀ f ∉ insert x L, ∀ r ∉ insert f (insert x L),
      (((Γ.cons x A).cons f (B.open x)).cons r ((C.open x).open f)).JEqB levels H (.univ n)
        (((D.open x).open f).open r) (((D.open x).open f).open r))
    (hK : ∀ x ∉ L, ∀ f ∉ insert x L, ∀ r ∉ insert f (insert x L),
      (((Γ.cons x A).cons f (B.open x)).cons r ((C.open x).open f)).JEqB levels H
        (((D.open x).open f).open r) (((K.open x).open f).open r) (((K.open x).open f).open r))
    (ha : Γ.JEqB levels H A a a) (hb : Γ.JEqB levels H (B.lst a) b b)
    (hc : Γ.JEqB levels H ((C.lst a).lst b) c c) :
    Γ.JEqB levels H (((D.lst a).lst b).lst c)
      (.app (.app (.app (.abs A (.abs B (.abs C K))) a) b) c) (((K.lst a).lst b).lst c) := by
  have hTail : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n)
      ((.pi B (.pi C D) : Tm 1).open x) ((.pi B (.pi C D) : Tm 1).open x) := by
    intro x hx
    simp only [Tm.open]
    apply Ctx.JEqB.pi hn (hB x hx)
    intro f hf
    simpa only [Tm.open] using Ctx.JEqB.pi hn (hC x hx f hf) (hD x hx f hf)
  have hInner : ∀ x ∉ L, (Γ.cons x A).JEqB levels H ((.pi B (.pi C D) : Tm 1).open x)
      ((.abs B (.abs C K) : Tm 1).open x) ((.abs B (.abs C K) : Tm 1).open x) := by
    intro x hx
    simp only [Tm.open]
    apply Ctx.JEqB.abs hn (hB x hx)
    · intro f hf
      simpa only [Tm.open] using Ctx.JEqB.pi hn (hC x hx f hf) (hD x hx f hf)
    · intro f hf
      simpa only [Tm.open] using Ctx.JEqB.abs hn (hC x hx f hf) (hD x hx f hf) (hK x hx f hf)
  have hFirst := Ctx.JEqB.beta_app hn hA hTail hInner ha
  simp only [Tm.lst] at hFirst
  have hBa : Γ.JEqB levels H (.univ n) (B.lst a) (B.lst a) := by
    simpa only [Tm.lst] using Ctx.JEqB.instantiate_of_hypotheses hH.weakening (fun x => hH.substitution x _) (B := .univ n) hΓ ha
      (by simpa only [Tm.open] using hB)
  obtain ⟨N, hCa⟩ := Ctx.JEqB.instantiate_two_retaining_one_of_hypotheses hH hn hΓ ha hB hC
  obtain ⟨M, hDa⟩ := Ctx.JEqB.instantiate_three_retaining_two_of_hypotheses hH hn hΓ hB hC hD ha
  obtain ⟨P, hKa⟩ := instantiate_under_two_dependent_of_hypotheses hH hn hΓ hB hC hK ha
  let Q := N ∪ M ∪ P
  have hCa' : ∀ f ∉ Q, (Γ.cons f (B.lst a)).JEqB levels H (.univ n)
      ((C.lst a).open f) ((C.lst a).open f) := by
    intro f hf
    exact hCa f (fun h => hf (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
  have hDa' : ∀ f ∉ Q, ∀ r ∉ insert f Q,
      ((Γ.cons f (B.lst a)).cons r ((C.lst a).open f)).JEqB levels H (.univ n)
        (((D.lst a).open f).open r) (((D.lst a).open f).open r) := by
    intro f hf r hr
    have hfM : f ∉ M := fun h => hf (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have hrM : r ∉ insert f M := by
      intro h
      apply hr
      exact (Finset.mem_insert.mp h).elim (fun q => Finset.mem_insert.mpr (Or.inl q))
        (fun q => Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_right _ q)))
    exact hDa f hfM r hrM
  have hKa' : ∀ f ∉ Q, ∀ r ∉ insert f Q,
      ((Γ.cons f (B.lst a)).cons r ((C.lst a).open f)).JEqB levels H
        (((D.lst a).open f).open r) (((K.lst a).open f).open r) (((K.lst a).open f).open r) := by
    intro f hf r hr
    have hfP : f ∉ P := fun h => hf (Finset.mem_union_right _ h)
    have hrP : r ∉ insert f P := by
      intro h
      apply hr
      exact (Finset.mem_insert.mp h).elim (fun q => Finset.mem_insert.mpr (Or.inl q))
        (fun q => Finset.mem_insert_of_mem (Finset.mem_union_right _ q))
    exact hKa f hfP r hrP
  have hTailA : ∀ f ∉ Q, (Γ.cons f (B.lst a)).JEqB levels H (.univ n)
      ((.pi (C.lst a) (D.lst a) : Tm 1).open f) ((.pi (C.lst a) (D.lst a) : Tm 1).open f) := by
    intro f hf
    simpa only [Tm.open] using Ctx.JEqB.pi hn (hCa' f hf) (hDa' f hf)
  have hSecond := Ctx.JEqB.app hn hBa hTailA hFirst hb
  simp only [Tm.lst] at hSecond
  have hCab : Γ.JEqB levels H (.univ n) ((C.lst a).lst b) ((C.lst a).lst b) := by
    simpa only [Tm.lst] using Ctx.JEqB.instantiate_of_hypotheses hH.weakening (fun x => hH.substitution x _) (B := .univ n) hΓ hb
      (by simpa only [Tm.open] using hCa')
  obtain ⟨R, hDab⟩ := Ctx.JEqB.instantiate_two_retaining_one_of_hypotheses hH hn hΓ hb hCa' hDa'
  exact (Ctx.JEqB.app hn hCab hDab hSecond hc).trans
    (doubleAbstraction_beta_of_hypotheses hH hn hΓ hBa hCa' hDa' hKa' hb hc)


theorem instantiate_two_retaining_one_dependent {levels : RuleBudget} {n : ℕ} {Γ : Ctx}
    {A a : Tm 0} {B : Tm 1} {D t u : Tm 2}
    {L : Finset String} {N : String → Finset String}
    (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (ha : Γ.JEqB levels ∅ A a a)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (ht : ∀ x ∉ L, ∀ y ∉ N x,
      ((Γ.cons x A).cons y (B.open x)).JEqB levels ∅
        ((D.open x).open y) ((t.open x).open y) ((u.open x).open y)) :
    ∃ M : Finset String, ∀ y ∉ M,
      (Γ.cons y (B.lst a)).JEqB levels ∅
        ((D.lst a).open y) ((t.lst a).open y) ((u.lst a).open y) :=
  instantiate_two_retaining_one_dependent_of_hypotheses (StructuralTheory.empty levels) hn hΓ ha hB ht

theorem instantiate_under_two_dependent {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A a : Tm 0}
    {B : Tm 1} {C : Tm 2} {D t u : Tm 3} {L : Finset String}
    (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (hC : ∀ x ∉ L, ∀ y ∉ insert x L,
      ((Γ.cons x A).cons y (B.open x)).JEqB levels ∅ (.univ n)
        ((C.open x).open y) ((C.open x).open y))
    (ht : ∀ x ∉ L, ∀ y ∉ insert x L, ∀ z ∉ insert y (insert x L),
      (((Γ.cons x A).cons y (B.open x)).cons z ((C.open x).open y)).JEqB levels ∅
        (((D.open x).open y).open z) (((t.open x).open y).open z) (((u.open x).open y).open z))
    (ha : Γ.JEqB levels ∅ A a a) :
    ∃ N : Finset String, ∀ y ∉ N, ∀ z ∉ insert y N,
      ((Γ.cons y (B.lst a)).cons z ((C.lst a).open y)).JEqB levels ∅
        (((D.lst a).open y).open z) (((t.lst a).open y).open z) (((u.lst a).open y).open z) :=
  instantiate_under_two_dependent_of_hypotheses (StructuralTheory.empty levels) hn hΓ hB hC ht ha

theorem doubleAbstraction_beta {levels : RuleBudget} {n : ℕ} {Γ : Ctx}
    {A a b : Tm 0} {B : Tm 1} {D K : Tm 2} {L : Finset String}
    (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (hD : ∀ x ∉ L, ∀ y ∉ insert x L,
      ((Γ.cons x A).cons y (B.open x)).JEqB levels ∅ (.univ n)
        ((D.open x).open y) ((D.open x).open y))
    (hK : ∀ x ∉ L, ∀ y ∉ insert x L,
      ((Γ.cons x A).cons y (B.open x)).JEqB levels ∅
        ((D.open x).open y) ((K.open x).open y) ((K.open x).open y))
    (ha : Γ.JEqB levels ∅ A a a) (hb : Γ.JEqB levels ∅ (B.lst a) b b) :
    Γ.JEqB levels ∅ ((D.lst a).lst b)
      (.app (.app (.abs A (.abs B K)) a) b) ((K.lst a).lst b) :=
  doubleAbstraction_beta_of_hypotheses (StructuralTheory.empty levels) hn hΓ hA hB hD hK ha hb

theorem tripleAbstraction_beta {levels : RuleBudget} {n : ℕ} {Γ : Ctx}
    {A a b c : Tm 0} {B : Tm 1} {C : Tm 2} {D K : Tm 3} {L : Finset String}
    (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (hC : ∀ x ∉ L, ∀ f ∉ insert x L,
      ((Γ.cons x A).cons f (B.open x)).JEqB levels ∅ (.univ n)
        ((C.open x).open f) ((C.open x).open f))
    (hD : ∀ x ∉ L, ∀ f ∉ insert x L, ∀ r ∉ insert f (insert x L),
      (((Γ.cons x A).cons f (B.open x)).cons r ((C.open x).open f)).JEqB levels ∅ (.univ n)
        (((D.open x).open f).open r) (((D.open x).open f).open r))
    (hK : ∀ x ∉ L, ∀ f ∉ insert x L, ∀ r ∉ insert f (insert x L),
      (((Γ.cons x A).cons f (B.open x)).cons r ((C.open x).open f)).JEqB levels ∅
        (((D.open x).open f).open r) (((K.open x).open f).open r) (((K.open x).open f).open r))
    (ha : Γ.JEqB levels ∅ A a a) (hb : Γ.JEqB levels ∅ (B.lst a) b b)
    (hc : Γ.JEqB levels ∅ ((C.lst a).lst b) c c) :
    Γ.JEqB levels ∅ (((D.lst a).lst b).lst c)
      (.app (.app (.app (.abs A (.abs B (.abs C K))) a) b) c) (((K.lst a).lst b).lst c) :=
  tripleAbstraction_beta_of_hypotheses (StructuralTheory.empty levels) hn hΓ hA hB hC hD hK ha hb hc

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
