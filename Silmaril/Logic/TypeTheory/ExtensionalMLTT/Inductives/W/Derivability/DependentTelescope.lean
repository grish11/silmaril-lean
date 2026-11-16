module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Instantiation
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Telescope
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.DependentTelescopeBeta

@[expose] public section

/-! Same-budget dependent telescope substitution and normalized multi-application beta. -/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

theorem Ctx.JEqB.instantiate_two_retaining_one_dependent_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hH : StructuralTheory levels H) {Γ : Ctx}
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
        ((D.lst a).open y) ((t.lst a).open y) ((u.lst a).open y) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.instantiate_two_retaining_one_dependent_of_hypotheses hH hn hΓ ha hB ht

theorem Ctx.JEqB.instantiate_under_two_dependent_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hH : StructuralTheory levels H) {Γ : Ctx} {A a : Tm 0}
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
        (((D.lst a).open y).open z) (((t.lst a).open y).open z) (((u.lst a).open y).open z) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.instantiate_under_two_dependent_of_hypotheses hH hn hΓ hB hC ht ha

theorem Ctx.JEqB.doubleAbstraction_beta_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hH : StructuralTheory levels H) {Γ : Ctx}
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
      (.app (.app (.abs A (.abs B K)) a) b) ((K.lst a).lst b) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.doubleAbstraction_beta_of_hypotheses hH hn hΓ hA hB hD hK ha hb

theorem Ctx.JEqB.tripleAbstraction_beta_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hH : StructuralTheory levels H) {Γ : Ctx}
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
      (.app (.app (.app (.abs A (.abs B (.abs C K))) a) b) c) (((K.lst a).lst b).lst c) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.tripleAbstraction_beta_of_hypotheses hH hn hΓ hA hB hC hD hK ha hb hc

theorem Ctx.JEqB.instantiate_two_retaining_one_dependent {levels : RuleBudget} {n : ℕ} {Γ : Ctx}
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
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.instantiate_two_retaining_one_dependent hn hΓ ha hB ht

theorem Ctx.JEqB.instantiate_under_two_dependent {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A a : Tm 0}
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
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.instantiate_under_two_dependent hn hΓ hB hC ht ha

theorem Ctx.JEqB.doubleAbstraction_beta {levels : RuleBudget} {n : ℕ} {Γ : Ctx}
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
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.doubleAbstraction_beta hn hΓ hA hB hD hK ha hb

theorem Ctx.JEqB.tripleAbstraction_beta {levels : RuleBudget} {n : ℕ} {Γ : Ctx}
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
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.tripleAbstraction_beta hn hΓ hA hB hC hD hK ha hb hc

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
