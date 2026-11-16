module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Head

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

private theorem single_shift (B : Tm 1) :
    B.bsubst (fun _ => .bv (1 : Fin 2)) = B.wk0 := by
  rw [Tm.wk0, Tm.wkn_eq_bsubst]
  congr 1
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

private theorem stepType_constant (A I : Tm 0) (B : Tm 1) :
    Tm.wStepType A B I.wk0 =
      .pi A (Tm.arr (Tm.arr B ((.wtype A B : Tm 0).castLE (by decide)))
        (Tm.arr (Tm.arr B (I.castLE (by decide))) (I.castLE (by decide)))) := by
  have hI : I.wk0 = I.castLE (Nat.zero_le 1) := Tm.wkn_past I 0 (Nat.le_refl 0)
  rw [hI]
  simp only [Tm.wStepType, Tm.bsubst_closed_castLE, single_shift,
    Tm.arr, Tm.wk0, Tm.wkn, Tm.closed_castLE_wkn]

private theorem arrow_open (A B : Tm 1) (x : String) :
    (Tm.arr A B).open x = Tm.arr (A.open x) (B.open x) := by
  simp only [Tm.arr, Tm.open, Tm.wk0, Tm.open_wkn B x 0 (Nat.zero_le _)]

private theorem step_open (A I : Tm 0) (B : Tm 1) (K : Tm 3) (x : String) :
    ((.abs (Tm.arr B ((.wtype A B : Tm 0).castLE (by decide)))
      (.abs ((Tm.arr B (I.castLE (by decide))).wk0) K) : Tm 1).open x) =
      .abs (Tm.arr (B.open x) (.wtype A B))
        (.abs ((Tm.arr (B.open x) I).wk0) (K.open x)) := by
  simp only [Tm.open, arrow_open, Tm.closed_castLE_open, Tm.castLE_refl,
    Tm.wk0, Tm.open_wkn _ x 0 (Nat.zero_le _)]

theorem arrow_abstraction_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hh : HypothesisTransport levels H H) {Γ : Ctx} {A I : Tm 0} {b : Tm 1}
    {L : Finset String} (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hI : Γ.JEqB levels H (.univ n) I I)
    (hb : ∀ x ∉ L, (Γ.cons x A).JEqB levels H I (b.open x) (b.open x)) :
    Γ.JEqB levels H (Tm.arr A I) (.abs A b) (.abs A b) := by
  apply Ctx.JEqB.abs (L := L ∪ Γ.dv) hn hA
  · intro x hx
    exact Ctx.JEqB.constant_family_of_hypotheses hh hn hΓ hA hI x
      (fun h => hx (Finset.mem_union_right _ h))
  · intro x hx
    simpa only [Tm.closed_wk0_open] using hb x
      (fun h => hx (Finset.mem_union_left _ h))

/-- Apply an actual nondependent function to an actual argument. -/
theorem arrow_application_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hh : HypothesisTransport levels H H) {Γ : Ctx} {A I f a : Tm 0}
    (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hI : Γ.JEqB levels H (.univ n) I I)
    (hf : Γ.JEqB levels H (.arr A I) f f) (ha : Γ.JEqB levels H A a a) :
    Γ.JEqB levels H I (.app f a) (.app f a) := by
  simpa only [Tm.closed_wk0_lst] using
    Ctx.JEqB.app hn hA (Ctx.JEqB.constant_family_of_hypotheses hh hn hΓ hA hI) hf ha

/-- A constant-motive W step may use the children and recursive hypotheses. -/
private theorem constantStep_local_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hh : HypothesisTransport levels H H) {Γ : Ctx} {A I : Tm 0} {B : Tm 1}
    {K : Tm 3} {L : Finset String} (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hI : Γ.JEqB levels H (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hK : ∀ x ∉ L, ∀ f ∉ insert x L, ∀ r ∉ insert f (insert x L),
      (((Γ.cons x A).cons f (Tm.arr (B.open x) (.wtype A B))).cons r
        (Tm.arr (B.open x) I)).JEqB levels H I
        (((K.open x).open f).open r) (((K.open x).open f).open r)) :
    ∀ x ∉ L ∪ Γ.dv,
      (Γ.cons x A).JEqB levels H (.univ n)
        (Tm.arr (Tm.arr (B.open x) (.wtype A B)) (Tm.arr (Tm.arr (B.open x) I) I))
        (Tm.arr (Tm.arr (B.open x) (.wtype A B)) (Tm.arr (Tm.arr (B.open x) I) I)) ∧
      (Γ.cons x A).JEqB levels H
        (Tm.arr (Tm.arr (B.open x) (.wtype A B)) (Tm.arr (Tm.arr (B.open x) I) I))
        (.abs (Tm.arr (B.open x) (.wtype A B))
          (.abs ((Tm.arr (B.open x) I).wk0) (K.open x)))
        (.abs (Tm.arr (B.open x) (.wtype A B))
          (.abs ((Tm.arr (B.open x) I).wk0) (K.open x))) := by
  have hW : Γ.JEqB levels H (.univ n) (.wtype A B) (.wtype A B) := .wtype hn hA hB
  intro x hx
  have hxL : x ∉ L := fun h => hx (Finset.mem_union_left _ h)
  have hxΓ : x ∉ Γ.dv := fun h => hx (Finset.mem_union_right _ h)
  have hctx : (Γ.cons x A).JEqB levels H .unit .star .star := .cons_ok hn hΓ hxΓ hA
  have hI' : (Γ.cons x A).JEqB levels H (.univ n) I I := hΓ.weaken_cons_of_hypotheses hh hxΓ hn hA hI
  have hW' : (Γ.cons x A).JEqB levels H (.univ n) (.wtype A B) (.wtype A B) :=
    hΓ.weaken_cons_of_hypotheses hh hxΓ hn hA hW
  have hF := Ctx.JEqB.arrow_formation_of_hypotheses hh hn hctx (hB x hxL) hW'
  have hR := Ctx.JEqB.arrow_formation_of_hypotheses hh hn hctx (hB x hxL) hI'
  have hRI := Ctx.JEqB.arrow_formation_of_hypotheses hh hn hctx hR hI'
  have houter : (Γ.cons x A).JEqB levels H
      (Tm.arr (Tm.arr (B.open x) (.wtype A B)) (Tm.arr (Tm.arr (B.open x) I) I))
      (.abs (Tm.arr (B.open x) (.wtype A B)) (.abs ((Tm.arr (B.open x) I).wk0) (K.open x)))
      (.abs (Tm.arr (B.open x) (.wtype A B)) (.abs ((Tm.arr (B.open x) I).wk0) (K.open x))) := by
    apply arrow_abstraction_of_hypotheses hh (L := insert x (L ∪ Γ.dv)) hn hctx hF hRI
    intro f hf
    have hfParts : f ≠ x ∧ f ∉ L ∧ f ∉ Γ.dv := by
      simpa only [Finset.mem_insert, Finset.mem_union, not_or] using hf
    have hfCtx : f ∉ (Γ.cons x A).dv := by
      simpa only [Ctx.dv, Finset.mem_insert, not_or] using And.intro hfParts.1 hfParts.2.2
    have hfL : f ∉ insert x L := fun h => hf (by
      simpa only [Finset.mem_insert, Finset.mem_union] using
        (show f = x ∨ f ∈ L ∨ f ∈ Γ.dv from (Finset.mem_insert.mp h).elim Or.inl (fun q => Or.inr (Or.inl q))))
    have hctxF : ((Γ.cons x A).cons f (Tm.arr (B.open x) (.wtype A B))).JEqB
        levels H .unit .star .star := .cons_ok hn hctx hfCtx hF
    have hRF := hctx.weaken_cons_of_hypotheses hh hfCtx hn hF hR
    have hIF := hctx.weaken_cons_of_hypotheses hh hfCtx hn hF hI'
    have hinner : ((Γ.cons x A).cons f (Tm.arr (B.open x) (.wtype A B))).JEqB levels H
        (Tm.arr (Tm.arr (B.open x) I) I)
        (.abs (Tm.arr (B.open x) I) ((K.open x).open f))
        (.abs (Tm.arr (B.open x) I) ((K.open x).open f)) :=
      arrow_abstraction_of_hypotheses hh hn hctxF hRF hIF (fun r hr => hK x hxL f hfL r hr)
    simpa only [Tm.open, Tm.closed_wk0_open] using hinner
  exact ⟨Ctx.JEqB.arrow_formation_of_hypotheses hh hn hctx hF hRI, houter⟩

theorem constantStep_typing_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hh : HypothesisTransport levels H H) {Γ : Ctx} {A I : Tm 0} {B : Tm 1}
    {K : Tm 3} {L : Finset String} (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hI : Γ.JEqB levels H (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hK : ∀ x ∉ L, ∀ f ∉ insert x L, ∀ r ∉ insert f (insert x L),
      (((Γ.cons x A).cons f (Tm.arr (B.open x) (.wtype A B))).cons r
        (Tm.arr (B.open x) I)).JEqB levels H I
        (((K.open x).open f).open r) (((K.open x).open f).open r)) :
    Γ.JEqB levels H (Tm.wStepType A B I.wk0)
      (.abs A (.abs (Tm.arr B ((.wtype A B : Tm 0).castLE (by decide)))
        (.abs ((Tm.arr B (I.castLE (by decide))).wk0) K)))
      (.abs A (.abs (Tm.arr B ((.wtype A B : Tm 0).castLE (by decide)))
        (.abs ((Tm.arr B (I.castLE (by decide))).wk0) K))) := by
  have hlocal := constantStep_local_of_hypotheses hh hn hΓ hA hI hB hK
  rw [stepType_constant]
  apply Ctx.JEqB.abs (L := L ∪ Γ.dv) hn hA
  · intro x hx
    simpa only [arrow_open, Tm.closed_castLE_open, Tm.castLE_refl] using (hlocal x hx).1
  · intro x hx
    simpa only [step_open, arrow_open, Tm.closed_castLE_open, Tm.castLE_refl] using (hlocal x hx).2

/-- The first object beta step of an arbitrary constant-motive W step. -/
theorem constantStep_first_beta_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hh : HypothesisTransport levels H H) {Γ : Ctx} {A I a : Tm 0} {B : Tm 1}
    {K : Tm 3} {L : Finset String} (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hI : Γ.JEqB levels H (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hK : ∀ x ∉ L, ∀ f ∉ insert x L, ∀ r ∉ insert f (insert x L),
      (((Γ.cons x A).cons f (Tm.arr (B.open x) (.wtype A B))).cons r
        (Tm.arr (B.open x) I)).JEqB levels H I
        (((K.open x).open f).open r) (((K.open x).open f).open r))
    (ha : Γ.JEqB levels H A a a) :
    Γ.JEqB levels H
      (.arr (.arr (B.lst a) (.wtype A B)) (.arr (.arr (B.lst a) I) I))
      (.app (.abs A (.abs (Tm.arr B ((.wtype A B : Tm 0).castLE (by decide)))
        (.abs ((Tm.arr B (I.castLE (by decide))).wk0) K))) a)
      (.abs (.arr (B.lst a) (.wtype A B))
        (.abs ((Tm.arr (B.lst a) I).wk0) (K.lst a))) := by
  let E : Tm 1 := .arr (.arr B ((.wtype A B : Tm 0).castLE (by decide)))
    (.arr (.arr B (I.castLE (by decide))) (I.castLE (by decide)))
  let T : Tm 1 := .abs (Tm.arr B ((.wtype A B : Tm 0).castLE (by decide)))
    (.abs ((Tm.arr B (I.castLE (by decide))).wk0) K)
  have hlocal := constantStep_local_of_hypotheses hh hn hΓ hA hI hB hK
  have hE : ∀ x ∉ L ∪ Γ.dv, (Γ.cons x A).JEqB levels H (.univ n)
      (E.open x) (E.open x) := by
    intro x hx
    simpa only [E, arrow_open, Tm.closed_castLE_open, Tm.castLE_refl] using (hlocal x hx).1
  have hT : ∀ x ∉ L ∪ Γ.dv, (Γ.cons x A).JEqB levels H (E.open x)
      (T.open x) (T.open x) := by
    intro x hx
    simpa only [T, E, step_open, arrow_open, Tm.closed_castLE_open, Tm.castLE_refl] using (hlocal x hx).2
  have hfirst : Γ.JEqB levels H (E.lst a) (.app (.abs A T) a) (T.lst a) :=
    .beta_app hn hA hE hT ha
  simpa only [E, T, Tm.arrow_lst, Tm.closed_castLE_lst, Tm.castLE_refl,
    Tm.lst, Tm.wk0, Tm.lst_wkn _ a 0 (Nat.zero_le _)] using hfirst
theorem arrow_abstraction {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A I : Tm 0} {b : Tm 1}
    {L : Finset String} (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A) (hI : Γ.JEqB levels ∅ (.univ n) I I)
    (hb : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ I (b.open x) (b.open x)) :
    Γ.JEqB levels ∅ (Tm.arr A I) (.abs A b) (.abs A b) :=
  arrow_abstraction_of_hypotheses (HypothesisTransport.empty levels ∅) hn hΓ hA hI hb

theorem arrow_application {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A I f a : Tm 0}
    (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A) (hI : Γ.JEqB levels ∅ (.univ n) I I)
    (hf : Γ.JEqB levels ∅ (.arr A I) f f) (ha : Γ.JEqB levels ∅ A a a) :
    Γ.JEqB levels ∅ I (.app f a) (.app f a) :=
  arrow_application_of_hypotheses (HypothesisTransport.empty levels ∅) hn hΓ hA hI hf ha

theorem constantStep_typing {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A I : Tm 0} {B : Tm 1}
    {K : Tm 3} {L : Finset String} (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A) (hI : Γ.JEqB levels ∅ (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (hK : ∀ x ∉ L, ∀ f ∉ insert x L, ∀ r ∉ insert f (insert x L),
      (((Γ.cons x A).cons f (Tm.arr (B.open x) (.wtype A B))).cons r
        (Tm.arr (B.open x) I)).JEqB levels ∅ I
        (((K.open x).open f).open r) (((K.open x).open f).open r)) :
    Γ.JEqB levels ∅ (Tm.wStepType A B I.wk0)
      (.abs A (.abs (Tm.arr B ((.wtype A B : Tm 0).castLE (by decide)))
        (.abs ((Tm.arr B (I.castLE (by decide))).wk0) K)))
      (.abs A (.abs (Tm.arr B ((.wtype A B : Tm 0).castLE (by decide)))
        (.abs ((Tm.arr B (I.castLE (by decide))).wk0) K))) :=
  constantStep_typing_of_hypotheses (HypothesisTransport.empty levels ∅) hn hΓ hA hI hB hK

theorem constantStep_first_beta {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A I a : Tm 0} {B : Tm 1}
    {K : Tm 3} {L : Finset String} (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A) (hI : Γ.JEqB levels ∅ (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (hK : ∀ x ∉ L, ∀ f ∉ insert x L, ∀ r ∉ insert f (insert x L),
      (((Γ.cons x A).cons f (Tm.arr (B.open x) (.wtype A B))).cons r
        (Tm.arr (B.open x) I)).JEqB levels ∅ I
        (((K.open x).open f).open r) (((K.open x).open f).open r))
    (ha : Γ.JEqB levels ∅ A a a) :
    Γ.JEqB levels ∅
      (.arr (.arr (B.lst a) (.wtype A B)) (.arr (.arr (B.lst a) I) I))
      (.app (.abs A (.abs (Tm.arr B ((.wtype A B : Tm 0).castLE (by decide)))
        (.abs ((Tm.arr B (I.castLE (by decide))).wk0) K))) a)
      (.abs (.arr (B.lst a) (.wtype A B))
        (.abs ((Tm.arr (B.lst a) I).wk0) (K.lst a))) :=
  constantStep_first_beta_of_hypotheses (HypothesisTransport.empty levels ∅) hn hΓ hA hI hB hK ha


end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
