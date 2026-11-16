module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.HeadComputation
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Telescope

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

private theorem arrow_open (A B : Tm 1) (x : String) :
    (Tm.arr A B).open x = Tm.arr (A.open x) (B.open x) := by
  simp only [Tm.arr, Tm.open, Tm.wk0, Tm.open_wkn B x 0 (Nat.zero_le _)]

private theorem double_open_wk0 (B : Tm 1) (x y : String) :
    (B.wk0.open x).open y = B.open x := by
  rw [Tm.wk0, Tm.open_wkn B x 0 (Nat.zero_le _)]
  exact Tm.closed_wk0_open (B.open x) y

private theorem lst_open_wk0 (B : Tm 1) (a : Tm 0) (x : String) :
    (B.wk0.lst a).open x = B.lst a := by
  rw [Tm.wk0, Tm.lst_wkn B a 0 (Nat.zero_le _)]
  exact Tm.closed_wk0_open (B.lst a) x

/-- All three object beta steps for a W step with arbitrary recursive body. -/
theorem constantStep_beta_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hH : StructuralTheory levels H) {Γ : Ctx} {A I a f r : Tm 0} {B : Tm 1}
    {K : Tm 3} {L : Finset String} (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hI : Γ.JEqB levels H (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hK : ∀ x ∉ L, ∀ f ∉ insert x L, ∀ r ∉ insert f (insert x L),
      (((Γ.cons x A).cons f (Tm.arr (B.open x) (.wtype A B))).cons r
        (Tm.arr (B.open x) I)).JEqB levels H I
        (((K.open x).open f).open r) (((K.open x).open f).open r))
    (ha : Γ.JEqB levels H A a a)
    (hf : Γ.JEqB levels H (.arr (B.lst a) (.wtype A B)) f f)
    (hr : Γ.JEqB levels H (.arr (B.lst a) I) r r) :
    Γ.JEqB levels H I
      (.app (.app (.app
        (.abs A (.abs (Tm.arr B ((.wtype A B : Tm 0).castLE (by decide)))
          (.abs ((Tm.arr B (I.castLE (by decide))).wk0) K))) a) f) r)
      (((K.lst a).lst f).lst r) := by
  let F : Tm 1 := .arr B ((.wtype A B : Tm 0).castLE (by decide))
  let R : Tm 1 := .arr B (I.castLE (by decide))
  have hW : Γ.JEqB levels H (.univ n) (.wtype A B) (.wtype A B) := .wtype hn hA hB
  have hP : Γ.JEqB levels H (.univ n) (B.lst a) (B.lst a) := by
    simpa only [Tm.lst] using Ctx.JEqB.instantiate_of_hypotheses hH.weakening (fun x => hH.substitution x _) (B := .univ n) hΓ ha
      (fun x hx => by simpa only [Tm.open] using hB x hx)
  have hFa : Γ.JEqB levels H (.univ n) (.arr (B.lst a) (.wtype A B))
      (.arr (B.lst a) (.wtype A B)) := Ctx.JEqB.arrow_formation_of_hypotheses hH.weakening hn hΓ hP hW
  have hHa : Γ.JEqB levels H (.univ n) (.arr (B.lst a) I) (.arr (B.lst a) I) :=
    Ctx.JEqB.arrow_formation_of_hypotheses hH.weakening hn hΓ hP hI
  have hHI : Γ.JEqB levels H (.univ n) (.arr (.arr (B.lst a) I) I)
      (.arr (.arr (B.lst a) I) I) := Ctx.JEqB.arrow_formation_of_hypotheses hH.weakening hn hΓ hHa hI
  have hFfamily : ∀ x ∉ L ∪ Γ.dv, (Γ.cons x A).JEqB levels H (.univ n)
      (F.open x) (F.open x) := by
    intro x hx
    have hxL : x ∉ L := fun h => hx (Finset.mem_union_left _ h)
    have hxΓ : x ∉ Γ.dv := fun h => hx (Finset.mem_union_right _ h)
    have hctx : (Γ.cons x A).JEqB levels H .unit .star .star := .cons_ok hn hΓ hxΓ hA
    simpa only [F, arrow_open, Tm.closed_castLE_open, Tm.castLE_refl] using
      Ctx.JEqB.arrow_formation_of_hypotheses hH.weakening hn hctx (hB x hxL) (hΓ.weaken_cons_of_hypotheses hH.weakening hxΓ hn hA hW)
  have hHfamily : ∀ x ∉ L ∪ Γ.dv, (Γ.cons x A).JEqB levels H (.univ n)
      (R.open x) (R.open x) := by
    intro x hx
    have hxL : x ∉ L := fun h => hx (Finset.mem_union_left _ h)
    have hxΓ : x ∉ Γ.dv := fun h => hx (Finset.mem_union_right _ h)
    have hctx : (Γ.cons x A).JEqB levels H .unit .star .star := .cons_ok hn hΓ hxΓ hA
    simpa only [R, arrow_open, Tm.closed_castLE_open, Tm.castLE_refl] using
      Ctx.JEqB.arrow_formation_of_hypotheses hH.weakening hn hctx (hB x hxL) (hΓ.weaken_cons_of_hypotheses hH.weakening hxΓ hn hA hI)
  have hHretained : ∀ x ∉ L ∪ Γ.dv, ∀ y ∉ insert x (L ∪ Γ.dv),
      ((Γ.cons x A).cons y (F.open x)).JEqB levels H (.univ n)
        ((R.wk0.open x).open y) ((R.wk0.open x).open y) := by
    intro x hx y hy
    have hxΓ : x ∉ Γ.dv := fun h => hx (Finset.mem_union_right _ h)
    have hyParts : y ≠ x ∧ y ∉ L ∧ y ∉ Γ.dv := by
      simpa only [Finset.mem_insert, Finset.mem_union, not_or] using hy
    have hyΓ : y ∉ (Γ.cons x A).dv := by
      simpa only [Ctx.dv, Finset.mem_insert, not_or] using And.intro hyParts.1 hyParts.2.2
    have hctx : (Γ.cons x A).JEqB levels H .unit .star .star := .cons_ok hn hΓ hxΓ hA
    simpa only [double_open_wk0] using
      hctx.weaken_cons_of_hypotheses hH.weakening hyΓ hn (hFfamily x hx) (hHfamily x hx)
  have hKsource : ∀ x ∉ L ∪ Γ.dv, ∀ y ∉ insert x (L ∪ Γ.dv),
      ∀ z ∉ insert y (insert x (L ∪ Γ.dv)),
      (((Γ.cons x A).cons y (F.open x)).cons z ((R.wk0.open x).open y)).JEqB levels H I
        (((K.open x).open y).open z) (((K.open x).open y).open z) := by
    intro x hx y hy z hz
    have hxL : x ∉ L := fun h => hx (Finset.mem_union_left _ h)
    have hyL : y ∉ insert x L := fun h => hy (Finset.mem_insert.mpr
      ((Finset.mem_insert.mp h).elim Or.inl (fun q => Or.inr (Finset.mem_union_left _ q))))
    have hzL : z ∉ insert y (insert x L) := by
      intro h
      rcases Finset.mem_insert.mp h with h | h
      · exact hz (Finset.mem_insert.mpr (Or.inl h))
      · exact hz (Finset.mem_insert_of_mem (Finset.mem_insert.mpr
          ((Finset.mem_insert.mp h).elim Or.inl (fun q => Or.inr (Finset.mem_union_left _ q)))))
    simpa only [F, R, double_open_wk0, arrow_open, Tm.closed_castLE_open, Tm.castLE_refl] using
      hK x hxL y hyL z hzL
  obtain ⟨M, hM⟩ := Ctx.JEqB.instantiate_three_retaining_two_of_hypotheses hH hn hΓ hFfamily hHretained hKsource ha
  have hMa : ∀ y ∉ M, ∀ z ∉ insert y M,
      ((Γ.cons y (.arr (B.lst a) (.wtype A B))).cons z (.arr (B.lst a) I)).JEqB levels H I
        (((K.lst a).open y).open z) (((K.lst a).open y).open z) := by
    simpa only [F, R, lst_open_wk0, Tm.arrow_lst, Tm.closed_castLE_lst, Tm.castLE_refl] using hM
  have hHafterA : ∀ y ∉ M ∪ Γ.dv,
      (Γ.cons y (.arr (B.lst a) (.wtype A B))).JEqB levels H (.univ n)
        ((Tm.arr (B.lst a) I).wk0.open y) ((Tm.arr (B.lst a) I).wk0.open y) := by
    intro y hy
    exact Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn hΓ hFa hHa y
      (fun h => hy (Finset.mem_union_right _ h))
  obtain ⟨N, hN⟩ := Ctx.JEqB.instantiate_two_retaining_one_of_hypotheses hH
    (I := I) (t := K.lst a) (u := K.lst a) (K := fun y => insert y M) hn hΓ hf hHafterA
    (fun y hy z hz => by
      simpa only [Tm.closed_wk0_open] using hMa y (fun h => hy (Finset.mem_union_left _ h)) z hz)
  have hN' : ∀ z ∉ N, (Γ.cons z (.arr (B.lst a) I)).JEqB levels H I
      ((((K.lst a).lst f).open z)) ((((K.lst a).lst f).open z)) := by
    simpa only [Tm.closed_wk0_lst] using hN
  have hbodyF : ∀ y ∉ M ∪ Γ.dv,
      (Γ.cons y (.arr (B.lst a) (.wtype A B))).JEqB levels H
        ((Tm.arr (.arr (B.lst a) I) I).wk0.open y)
        ((.abs ((Tm.arr (B.lst a) I).wk0) (K.lst a) : Tm 1).open y)
        ((.abs ((Tm.arr (B.lst a) I).wk0) (K.lst a) : Tm 1).open y) := by
    intro y hy
    have hyΓ : y ∉ Γ.dv := fun h => hy (Finset.mem_union_right _ h)
    have hctx : (Γ.cons y (.arr (B.lst a) (.wtype A B))).JEqB levels H .unit .star .star :=
      .cons_ok hn hΓ hyΓ hFa
    have hinner := Ctx.JEqB.arrow_abstraction_of_hypotheses hH.weakening hn hctx (hΓ.weaken_cons_of_hypotheses hH.weakening hyΓ hn hFa hHa)
      (hΓ.weaken_cons_of_hypotheses hH.weakening hyΓ hn hFa hI)
      (hMa y (fun h => hy (Finset.mem_union_left _ h)))
    simpa only [Tm.open, Tm.closed_wk0_open] using hinner
  have hsecond : Γ.JEqB levels H (.arr (.arr (B.lst a) I) I)
      (.app (.abs (.arr (B.lst a) (.wtype A B))
        (.abs ((Tm.arr (B.lst a) I).wk0) (K.lst a))) f)
      (.abs (.arr (B.lst a) I) ((K.lst a).lst f)) := by
    simpa only [Tm.closed_wk0_lst, Tm.lst] using Ctx.JEqB.beta_app (L := M ∪ Γ.dv) hn hFa
      (fun y hy => Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn hΓ hFa hHI y
        (fun h => hy (Finset.mem_union_right _ h))) hbodyF hf
  have hthird : Γ.JEqB levels H I
      (.app (.abs (.arr (B.lst a) I) ((K.lst a).lst f)) r)
      (((K.lst a).lst f).lst r) := by
    simpa only [Tm.closed_wk0_lst] using Ctx.JEqB.beta_app (L := N ∪ Γ.dv) hn hHa
      (fun z hz => Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn hΓ hHa hI z
        (fun h => hz (Finset.mem_union_right _ h)))
      (fun z hz => by
        simpa only [Tm.closed_wk0_open] using hN' z (fun h => hz (Finset.mem_union_left _ h))) hr
  let step : Tm 0 := .abs A (.abs (Tm.arr B ((.wtype A B : Tm 0).castLE (by decide)))
    (.abs ((Tm.arr B (I.castLE (by decide))).wk0) K))
  let tail : Tm 0 := .abs (.arr (B.lst a) (.wtype A B))
    (.abs ((Tm.arr (B.lst a) I).wk0) (K.lst a))
  have hfirst : Γ.JEqB levels H
      (.arr (.arr (B.lst a) (.wtype A B)) (.arr (.arr (B.lst a) I) I))
      (.app step a) tail := Ctx.JEqB.constantStep_first_beta_of_hypotheses hH.weakening hn hΓ hA hI hB hK ha
  have hfirstF : Γ.JEqB levels H (.arr (.arr (B.lst a) I) I)
      (.app (.app step a) f) (.app tail f) := by
    simpa only [Tm.closed_wk0_lst] using
      Ctx.JEqB.app hn hFa (Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn hΓ hFa hHI) hfirst hf
  have hfirstR : Γ.JEqB levels H I (.app (.app (.app step a) f) r)
      (.app (.app tail f) r) := by
    simpa only [Tm.closed_wk0_lst] using
      Ctx.JEqB.app hn hHa (Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn hΓ hHa hI) hfirstF hr
  have hsecondR : Γ.JEqB levels H I (.app (.app tail f) r)
      (.app (.abs (.arr (B.lst a) I) ((K.lst a).lst f)) r) := by
    simpa only [Tm.closed_wk0_lst] using
      Ctx.JEqB.app hn hHa (Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn hΓ hHa hI) hsecond hr
  exact hfirstR.trans (hsecondR.trans hthird)

theorem constantStep_beta {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A I a f r : Tm 0} {B : Tm 1}
    {K : Tm 3} {L : Finset String} (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A) (hI : Γ.JEqB levels ∅ (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (hK : ∀ x ∉ L, ∀ f ∉ insert x L, ∀ r ∉ insert f (insert x L),
      (((Γ.cons x A).cons f (Tm.arr (B.open x) (.wtype A B))).cons r
        (Tm.arr (B.open x) I)).JEqB levels ∅ I
        (((K.open x).open f).open r) (((K.open x).open f).open r))
    (ha : Γ.JEqB levels ∅ A a a)
    (hf : Γ.JEqB levels ∅ (.arr (B.lst a) (.wtype A B)) f f)
    (hr : Γ.JEqB levels ∅ (.arr (B.lst a) I) r r) :
    Γ.JEqB levels ∅ I
      (.app (.app (.app
        (.abs A (.abs (Tm.arr B ((.wtype A B : Tm 0).castLE (by decide)))
          (.abs ((Tm.arr B (I.castLE (by decide))).wk0) K))) a) f) r)
      (((K.lst a).lst f).lst r) :=
  constantStep_beta_of_hypotheses (StructuralTheory.empty levels) hn hΓ hA hI hB hK ha hf hr

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
