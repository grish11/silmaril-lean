module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Substitution
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.TelescopeInstantiation

@[expose] public section

/-! Same-bound instantiation through retained dependent declarations. -/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

theorem Ctx.JEqB.instantiate_two_retaining_one_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hH : StructuralTheory levels H) {Γ : Ctx}
    {A I a : Tm 0} {B : Tm 1} {t u : Tm 2}
    {L : Finset String} {K : String → Finset String}
    (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels H .unit .star .star)
    (ha : Γ.JEqB levels H A a a)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (ht : ∀ x ∉ L, ∀ y ∉ K x,
      ((Γ.cons x A).cons y (B.open x)).JEqB levels H I
        ((t.open x).open y) ((u.open x).open y)) :
    ∃ N : Finset String, ∀ y ∉ N,
      (Γ.cons y (B.lst a)).JEqB levels H I ((t.lst a).open y) ((u.lst a).open y) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.instantiate_two_retaining_one_of_hypotheses hH hn hΓ ha hB ht

theorem Ctx.JEqB.instantiate_two_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hH : StructuralTheory levels H) {Γ : Ctx}
    {A I a b : Tm 0} {B : Tm 1} {t u : Tm 2}
    {L : Finset String} {K : String → Finset String}
    (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels H .unit .star .star)
    (ha : Γ.JEqB levels H A a a) (hb : Γ.JEqB levels H (B.lst a) b b)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (ht : ∀ x ∉ L, ∀ y ∉ K x,
      ((Γ.cons x A).cons y (B.open x)).JEqB levels H I
        ((t.open x).open y) ((u.open x).open y)) :
    Γ.JEqB levels H I ((t.lst a).lst b) ((u.lst a).lst b) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.instantiate_two_of_hypotheses hH hn hΓ ha hb hB ht

theorem Ctx.JEqB.instantiate_three_retaining_two_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hH : StructuralTheory levels H) {Γ : Ctx} {A I a : Tm 0}
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
        (((t.lst a).open y).open z) (((u.lst a).open y).open z) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.instantiate_under_two_of_hypotheses hH hn hΓ hB hC ht ha

theorem Ctx.JEqB.instantiate_three_retaining_one_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hH : StructuralTheory levels H) {Γ : Ctx} {A I a b : Tm 0}
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
        ((((t.lst a).lst b).open z)) ((((u.lst a).lst b).open z)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.instantiate_three_retaining_one_of_hypotheses hH hn hΓ hB hC ht ha hb

theorem Ctx.JEqB.instantiate_three_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hH : StructuralTheory levels H) {Γ : Ctx} {A I a b c : Tm 0}
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
    Γ.JEqB levels H I (((t.lst a).lst b).lst c) (((u.lst a).lst b).lst c) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.instantiate_three_of_hypotheses hH hn hΓ hB hC ht ha hb hc

theorem Ctx.JEqB.instantiate_two_retaining_one {levels : RuleBudget} {n : ℕ} {Γ : Ctx}
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
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.instantiate_two_retaining_one hn hΓ ha hB ht

theorem Ctx.JEqB.instantiate_two {levels : RuleBudget} {n : ℕ} {Γ : Ctx}
    {A I a b : Tm 0} {B : Tm 1} {t u : Tm 2}
    {L : Finset String} {K : String → Finset String}
    (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (ha : Γ.JEqB levels ∅ A a a) (hb : Γ.JEqB levels ∅ (B.lst a) b b)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (ht : ∀ x ∉ L, ∀ y ∉ K x,
      ((Γ.cons x A).cons y (B.open x)).JEqB levels ∅ I
        ((t.open x).open y) ((u.open x).open y)) :
    Γ.JEqB levels ∅ I ((t.lst a).lst b) ((u.lst a).lst b) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.instantiate_two hn hΓ ha hb hB ht

theorem Ctx.JEqB.instantiate_three_retaining_two {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A I a : Tm 0}
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
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.instantiate_under_two hn hΓ hB hC ht ha

theorem Ctx.JEqB.instantiate_three_retaining_one {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A I a b : Tm 0}
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
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.instantiate_three_retaining_one hn hΓ hB hC ht ha hb

theorem Ctx.JEqB.instantiate_three {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A I a b c : Tm 0}
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
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.instantiate_three hn hΓ hB hC ht ha hb hc

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
