module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.ConstantStep
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Substitution

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

variable {H : Set Jdg} {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A I s a f p : Tm 0} {B : Tm 1} {L : Finset String}

private theorem recChildren_body_open (A s f : Tm 0) (B C : Tm 1) (x : String) :
    ((.wrec A.wk0 (B.wkn 1) (C.wkn 1) s.wk0 (.app f.wk0 (.bv 0)) : Tm 1).open x) =
      .wrec A B C s (.app f (.fv x)) := by
  simp only [Tm.open, Tm.closed_wk0_open, Tm.wkn_past B 1 (Nat.le_refl 1),
    Tm.wkn_past C 1 (Nat.le_refl 1), Tm.open_castLE _ (Nat.le_refl 1), Tm.castLE_refl]
  congr 1

/-- The recursive argument supplied by constant-motive W computation is actually typed. -/
private theorem recChildren_body_typing (hH : StructuralTheory levels H) (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hI : Γ.JEqB levels H (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hs : Γ.JEqB levels H (Tm.wStepType A B I.wk0) s s)
    (ha : Γ.JEqB levels H A a a)
    (hf : Γ.JEqB levels H (.arr (B.lst a) (.wtype A B)) f f) :
    ∀ p ∉ Γ.dv, (Γ.cons p (B.lst a)).JEqB levels H (I.wk0.open p)
      ((.wrec A.wk0 (B.wkn 1) (I.wk0.wkn 1) s.wk0 (.app f.wk0 (.bv 0)) : Tm 1).open p)
      ((.wrec A.wk0 (B.wkn 1) (I.wk0.wkn 1) s.wk0 (.app f.wk0 (.bv 0)) : Tm 1).open p) := by
  have hP : Γ.JEqB levels H (.univ n) (B.lst a) (B.lst a) := by
    simpa only [Tm.open, Tm.lst] using
      Ctx.JEqB.instantiate_of_hypotheses hH.weakening (fun x => hH.substitution x _) (B := .univ n) hΓ ha
        (fun x hx => by simpa only [Tm.open] using hB x hx)
  have hW : Γ.JEqB levels H (.univ n) (.wtype A B) (.wtype A B) := .wtype hn hA hB
  intro p hp
  have hctx : (Γ.cons p (B.lst a)).JEqB levels H .unit .star .star := .cons_ok hn hΓ hp hP
  have e : Γ.LookupLE (Γ.cons p (B.lst a)) := Ctx.LookupLE.fresh_cons hp (B.lst a)
  have hA' : (Γ.cons p (B.lst a)).JEqB levels H (.univ n) A A := hA.weaken_of_hypotheses hH.weakening e hctx
  have hI' : (Γ.cons p (B.lst a)).JEqB levels H (.univ n) I I := hI.weaken_of_hypotheses hH.weakening e hctx
  have hW' : (Γ.cons p (B.lst a)).JEqB levels H (.univ n) (.wtype A B) (.wtype A B) :=
    hW.weaken_of_hypotheses hH.weakening e hctx
  have hB' : ∀ x ∉ L ∪ (Γ.cons p (B.lst a)).dv,
      ((Γ.cons p (B.lst a)).cons x A).JEqB levels H (.univ n) (B.open x) (B.open x) := by
    intro x hx
    have hxL : x ∉ L := fun h => hx (Finset.mem_union_left _ h)
    have hxΓ : x ∉ (Γ.cons p (B.lst a)).dv := fun h => hx (Finset.mem_union_right _ h)
    have hctxA : ((Γ.cons p (B.lst a)).cons x A).JEqB levels H .unit .star .star :=
      .cons_ok hn hctx hxΓ hA'
    exact (hB x hxL).weaken_of_hypotheses hH.weakening (Ctx.LookupLE.cons e x A) hctxA
  have hC : ∀ x ∉ L ∪ (Γ.cons p (B.lst a)).dv,
      ((Γ.cons p (B.lst a)).cons x (.wtype A B)).JEqB levels H (.univ n)
        (I.wk0.open x) (I.wk0.open x) := by
    intro x hx
    exact Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn hctx hW' hI' x
      (fun h => hx (Finset.mem_union_right _ h))
  have hchild : (Γ.cons p (B.lst a)).JEqB levels H (.wtype A B)
      (.app f (.fv p)) (.app f (.fv p)) :=
    Ctx.JEqB.arrow_application_of_hypotheses hH.weakening hn hctx (hP.weaken_of_hypotheses hH.weakening e hctx) hW' (hf.weaken_of_hypotheses hH.weakening e hctx)
      (.var hctx (.here Γ p (B.lst a)))
  simpa only [recChildren_body_open, Tm.closed_wk0_lst, Tm.closed_wk0_open] using
    Ctx.JEqB.wrec hn hn hA' hB' hC (hs.weaken_of_hypotheses hH.weakening e hctx) hchild

theorem recChildren_constant_typing_of_hypotheses (hH : StructuralTheory levels H) (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hI : Γ.JEqB levels H (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hs : Γ.JEqB levels H (Tm.wStepType A B I.wk0) s s)
    (ha : Γ.JEqB levels H A a a)
    (hf : Γ.JEqB levels H (.arr (B.lst a) (.wtype A B)) f f) :
    Γ.JEqB levels H (.arr (B.lst a) I)
      (Tm.recChildren A B I.wk0 s a f) (Tm.recChildren A B I.wk0 s a f) := by
  have hP : Γ.JEqB levels H (.univ n) (B.lst a) (B.lst a) := by
    simpa only [Tm.open, Tm.lst] using
      Ctx.JEqB.instantiate_of_hypotheses hH.weakening (fun x => hH.substitution x _) (B := .univ n) hΓ ha
        (fun x hx => by simpa only [Tm.open] using hB x hx)
  unfold Tm.recChildren
  apply Ctx.JEqB.arrow_abstraction_of_hypotheses hH.weakening hn hΓ hP hI
  simpa only [Tm.closed_wk0_open] using recChildren_body_typing hH hn hΓ hA hI hB hs ha hf

/-- Constant abstraction computes at an arbitrary actual argument. -/
theorem constant_abstraction_beta_of_hypotheses {b : Tm 0} (hH : StructuralTheory levels H) (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hI : Γ.JEqB levels H (.univ n) I I)
    (hb : Γ.JEqB levels H I b b) (ha : Γ.JEqB levels H A a a) :
    Γ.JEqB levels H I (.app (.abs A b.wk0) a) b := by
  have hbody : ∀ x ∉ Γ.dv, (Γ.cons x A).JEqB levels H (I.wk0.open x)
      (b.wk0.open x) (b.wk0.open x) := by
    intro x hx
    simpa only [Tm.closed_wk0_open] using hΓ.weaken_cons_of_hypotheses hH.weakening hx hn hA hb
  simpa only [Tm.closed_wk0_lst] using
    Ctx.JEqB.beta_app hn hA (Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn hΓ hA hI) hbody ha

private def headTailType (A I : Tm 0) (B : Tm 1) : Tm 1 :=
  .arr (.arr B ((.wtype A B : Tm 0).castLE (by decide)))
    (.arr (.arr B (I.castLE (by decide))) (I.castLE (by decide)))

private def headTail (A I : Tm 0) (B g : Tm 1) : Tm 1 :=
  .abs (.arr B ((.wtype A B : Tm 0).castLE (by decide)))
    ((Tm.abs (.arr B (I.castLE (by decide))) g.wk0).wk0)

private theorem arrow_open (A B : Tm 1) (x : String) :
    (Tm.arr A B).open x = Tm.arr (A.open x) (B.open x) := by
  simp only [Tm.arr, Tm.open, Tm.wk0, Tm.open_wkn B x 0 (Nat.zero_le _)]

private theorem headTail_open (A I : Tm 0) (B g : Tm 1) (x : String) :
    (headTail A I B g).open x =
      .abs (.arr (B.open x) (.wtype A B))
        ((Tm.abs (.arr (B.open x) I) (g.open x).wk0).wk0) := by
  simp only [headTail, Tm.open, arrow_open, Tm.closed_castLE_open, Tm.castLE_refl,
    Tm.wk0, Tm.open_wkn _ x 0 (Nat.zero_le _)]

private theorem headTail_data {g : Tm 1} (hH : StructuralTheory levels H) (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hI : Γ.JEqB levels H (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hg : ∀ x ∉ L, (Γ.cons x A).JEqB levels H I (g.open x) (g.open x)) :
    ∀ x ∉ L ∪ Γ.dv,
      (Γ.cons x A).JEqB levels H (.univ n)
        ((headTailType A I B).open x) ((headTailType A I B).open x) ∧
      (Γ.cons x A).JEqB levels H ((headTailType A I B).open x)
        ((headTail A I B g).open x) ((headTail A I B g).open x) := by
  intro x hx
  have hxL : x ∉ L := fun h => hx (Finset.mem_union_left _ h)
  have hxΓ : x ∉ Γ.dv := fun h => hx (Finset.mem_union_right _ h)
  have hW : Γ.JEqB levels H (.univ n) (.wtype A B) (.wtype A B) := .wtype hn hA hB
  have hctx : (Γ.cons x A).JEqB levels H .unit .star .star := .cons_ok hn hΓ hxΓ hA
  have hI' : (Γ.cons x A).JEqB levels H (.univ n) I I := hΓ.weaken_cons_of_hypotheses hH.weakening hxΓ hn hA hI
  have hW' : (Γ.cons x A).JEqB levels H (.univ n) (.wtype A B) (.wtype A B) :=
    hΓ.weaken_cons_of_hypotheses hH.weakening hxΓ hn hA hW
  have hF := Ctx.JEqB.arrow_formation_of_hypotheses hH.weakening hn hctx (hB x hxL) hW'
  have hR := Ctx.JEqB.arrow_formation_of_hypotheses hH.weakening hn hctx (hB x hxL) hI'
  have hRI := Ctx.JEqB.arrow_formation_of_hypotheses hH.weakening hn hctx hR hI'
  have hinner := Ctx.JEqB.constant_abstraction_of_hypotheses hH.weakening hn hctx hR hI' (hg x hxL)
  have houter := Ctx.JEqB.constant_abstraction_of_hypotheses hH.weakening hn hctx hF hRI hinner
  constructor
  · simpa only [headTailType, arrow_open, Tm.closed_castLE_open, Tm.castLE_refl] using
      Ctx.JEqB.arrow_formation_of_hypotheses hH.weakening hn hctx hF hRI
  · simpa only [headTailType, headTail_open, arrow_open, Tm.closed_castLE_open, Tm.castLE_refl] using houter

private theorem headStep_first_beta {g : Tm 1} (hH : StructuralTheory levels H) (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hI : Γ.JEqB levels H (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hg : ∀ x ∉ L, (Γ.cons x A).JEqB levels H I (g.open x) (g.open x))
    (ha : Γ.JEqB levels H A a a) :
    Γ.JEqB levels H ((headTailType A I B).lst a)
      (.app (Tm.headStep A B I g) a) ((headTail A I B g).lst a) :=
  .beta_app hn hA (fun x hx => (headTail_data hH hn hΓ hA hI hB hg x hx).1)
    (fun x hx => (headTail_data hH hn hΓ hA hI hB hg x hx).2) ha

private theorem headStep_body_lst (A I a : Tm 0) (B g : Tm 1) :
    (.abs (.arr B ((.wtype A B : Tm 0).castLE (by decide)))
      ((Tm.abs (.arr B (I.castLE (by decide))) g.wk0).wk0) : Tm 1).lst a =
      .abs (.arr (B.lst a) (.wtype A B))
        ((Tm.abs (.arr (B.lst a) I) ((g.lst a).wk0)).wk0) := by
  simp only [Tm.lst, Tm.arr, Tm.wk0,
    Tm.lst_wkn _ a 0 (Nat.zero_le _), Tm.closed_castLE_lst, Tm.castLE_refl]


/-- The generic root observer computes to its label body on every actual W node. -/
theorem head_beta_of_hypotheses {g : Tm 1} (hH : StructuralTheory levels H) (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hI : Γ.JEqB levels H (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hg : ∀ x ∉ L, (Γ.cons x A).JEqB levels H I (g.open x) (g.open x))
    (ha : Γ.JEqB levels H A a a)
    (hf : Γ.JEqB levels H (.arr (B.lst a) (.wtype A B)) f f) :
    Γ.JEqB levels H I (Tm.head A B I g (.sup A B a f)) (g.lst a) := by
  have hP : Γ.JEqB levels H (.univ n) (B.lst a) (B.lst a) := by
    simpa only [Tm.lst] using Ctx.JEqB.instantiate_of_hypotheses hH.weakening (fun x => hH.substitution x _) (B := .univ n) hΓ ha
      (fun x hx => by simpa only [Tm.open] using hB x hx)
  have hW : Γ.JEqB levels H (.univ n) (.wtype A B) (.wtype A B) := .wtype hn hA hB
  have hF : Γ.JEqB levels H (.univ n) (.arr (B.lst a) (.wtype A B))
      (.arr (B.lst a) (.wtype A B)) := Ctx.JEqB.arrow_formation_of_hypotheses hH.weakening hn hΓ hP hW
  have hR : Γ.JEqB levels H (.univ n) (.arr (B.lst a) I) (.arr (B.lst a) I) :=
    Ctx.JEqB.arrow_formation_of_hypotheses hH.weakening hn hΓ hP hI
  have hRI : Γ.JEqB levels H (.univ n) (.arr (.arr (B.lst a) I) I)
      (.arr (.arr (B.lst a) I) I) := Ctx.JEqB.arrow_formation_of_hypotheses hH.weakening hn hΓ hR hI
  have hga : Γ.JEqB levels H I (g.lst a) (g.lst a) := by
    simpa only [Tm.closed_wk0_lst] using Ctx.JEqB.instantiate_of_hypotheses hH.weakening (fun x => hH.substitution x _) (B := I.wk0) hΓ ha
      (fun x hx => by simpa only [Tm.closed_wk0_open] using hg x hx)
  have hstep : Γ.JEqB levels H (Tm.wStepType A B I.wk0)
      (Tm.headStep A B I g) (Tm.headStep A B I g) :=
    Ctx.JEqB.headStep_typing_of_hypotheses hH.weakening hn hΓ hA hI hB hg
  let R := Tm.recChildren A B I.wk0 (Tm.headStep A B I g) a f
  have hrecursive : Γ.JEqB levels H (.arr (B.lst a) I) R R :=
    recChildren_constant_typing_of_hypotheses hH hn hΓ hA hI hB hstep ha hf
  have hC : ∀ x ∉ L ∪ Γ.dv, (Γ.cons x (.wtype A B)).JEqB levels H (.univ n)
      (I.wk0.open x) (I.wk0.open x) := by
    intro x hx
    exact Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn hΓ hW hI x
      (fun h => hx (Finset.mem_union_right _ h))
  have hrec : Γ.JEqB levels H I (Tm.head A B I g (.sup A B a f))
      (.app (.app (.app (Tm.headStep A B I g) a) f) R) := by
    simpa only [Tm.head, Tm.closed_wk0_lst] using Ctx.JEqB.beta_wrec hn hn hA
      (fun x hx => hB x (fun h => hx (Finset.mem_union_left _ h))) hC hstep ha hf
  have hfirst : Γ.JEqB levels H
      (.arr (.arr (B.lst a) (.wtype A B)) (.arr (.arr (B.lst a) I) I))
      (.app (Tm.headStep A B I g) a)
      (.abs (.arr (B.lst a) (.wtype A B))
        ((Tm.abs (.arr (B.lst a) I) ((g.lst a).wk0)).wk0)) := by
    simpa only [headTailType, Tm.arrow_lst, Tm.closed_castLE_lst, Tm.castLE_refl,
      headTail, headStep_body_lst] using headStep_first_beta hH hn hΓ hA hI hB hg ha
  have hfirstF : Γ.JEqB levels H (.arr (.arr (B.lst a) I) I)
      (.app (.app (Tm.headStep A B I g) a) f)
      (.app (.abs (.arr (B.lst a) (.wtype A B))
        ((Tm.abs (.arr (B.lst a) I) ((g.lst a).wk0)).wk0)) f) := by
    simpa only [Tm.closed_wk0_lst] using Ctx.JEqB.app hn hF
      (Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn hΓ hF hRI) hfirst hf
  have hfirstR : Γ.JEqB levels H I
      (.app (.app (.app (Tm.headStep A B I g) a) f) R)
      (.app (.app (.abs (.arr (B.lst a) (.wtype A B))
        ((Tm.abs (.arr (B.lst a) I) ((g.lst a).wk0)).wk0)) f) R) := by
    simpa only [Tm.closed_wk0_lst] using Ctx.JEqB.app hn hR
      (Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn hΓ hR hI) hfirstF hrecursive
  have hinner : Γ.JEqB levels H (.arr (.arr (B.lst a) I) I)
      (.abs (.arr (B.lst a) I) ((g.lst a).wk0))
      (.abs (.arr (B.lst a) I) ((g.lst a).wk0)) :=
    Ctx.JEqB.constant_abstraction_of_hypotheses hH.weakening hn hΓ hR hI hga
  have hsecond : Γ.JEqB levels H (.arr (.arr (B.lst a) I) I)
      (.app (.abs (.arr (B.lst a) (.wtype A B))
        ((Tm.abs (.arr (B.lst a) I) ((g.lst a).wk0)).wk0)) f)
      (.abs (.arr (B.lst a) I) ((g.lst a).wk0)) :=
    constant_abstraction_beta_of_hypotheses hH hn hΓ hF hRI hinner hf
  have hsecondR : Γ.JEqB levels H I
      (.app (.app (.abs (.arr (B.lst a) (.wtype A B))
        ((Tm.abs (.arr (B.lst a) I) ((g.lst a).wk0)).wk0)) f) R)
      (.app (.abs (.arr (B.lst a) I) ((g.lst a).wk0)) R) := by
    simpa only [Tm.closed_wk0_lst] using Ctx.JEqB.app hn hR
      (Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn hΓ hR hI) hsecond hrecursive
  exact hrec.trans (hfirstR.trans (hsecondR.trans
    (constant_abstraction_beta_of_hypotheses hH hn hΓ hR hI hga hrecursive)))

private theorem recChildren_body_lst (A I s f p : Tm 0) (B : Tm 1) :
    ((.wrec A.wk0 (B.wkn 1) (I.wk0.wkn 1) s.wk0 (.app f.wk0 (.bv 0)) : Tm 1).lst p) =
      .wrec A B I.wk0 s (.app f p) := by
  simp only [Tm.lst, Tm.closed_wk0_lst, Tm.wkn_past B 1 (Nat.le_refl 1),
    Tm.wkn_past I.wk0 1 (Nat.le_refl 1), Tm.castLE_refl]
  congr 1
  · simpa only [Tm.castLE_refl] using Tm.lst_castLE B (Nat.le_refl 1) p
  · simpa only [Tm.castLE_refl] using Tm.lst_castLE I.wk0 (Nat.le_refl 1) p

theorem recChildren_constant_beta_of_hypotheses (hH : StructuralTheory levels H) (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hI : Γ.JEqB levels H (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hs : Γ.JEqB levels H (Tm.wStepType A B I.wk0) s s)
    (ha : Γ.JEqB levels H A a a)
    (hf : Γ.JEqB levels H (.arr (B.lst a) (.wtype A B)) f f)
    (hp : Γ.JEqB levels H (B.lst a) p p) :
    Γ.JEqB levels H I
      (.app (Tm.recChildren A B I.wk0 s a f) p)
      (.wrec A B I.wk0 s (.app f p)) := by
  have hP : Γ.JEqB levels H (.univ n) (B.lst a) (B.lst a) := by
    simpa only [Tm.open, Tm.lst] using
      Ctx.JEqB.instantiate_of_hypotheses hH.weakening (fun x => hH.substitution x _) (B := .univ n) hΓ ha
        (fun x hx => by simpa only [Tm.open] using hB x hx)
  have hbeta := Ctx.JEqB.beta_app hn hP
    (Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn hΓ hP hI) (recChildren_body_typing hH hn hΓ hA hI hB hs ha hf) hp
  simpa only [Tm.recChildren, Tm.closed_wk0_lst, recChildren_body_lst] using hbeta

theorem recChildren_constant_typing (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A) (hI : Γ.JEqB levels ∅ (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (hs : Γ.JEqB levels ∅ (Tm.wStepType A B I.wk0) s s)
    (ha : Γ.JEqB levels ∅ A a a)
    (hf : Γ.JEqB levels ∅ (.arr (B.lst a) (.wtype A B)) f f) :
    Γ.JEqB levels ∅ (.arr (B.lst a) I)
      (Tm.recChildren A B I.wk0 s a f) (Tm.recChildren A B I.wk0 s a f) :=
  recChildren_constant_typing_of_hypotheses (StructuralTheory.empty levels) hn hΓ hA hI hB hs ha hf

theorem constant_abstraction_beta {b : Tm 0} (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A) (hI : Γ.JEqB levels ∅ (.univ n) I I)
    (hb : Γ.JEqB levels ∅ I b b) (ha : Γ.JEqB levels ∅ A a a) :
    Γ.JEqB levels ∅ I (.app (.abs A b.wk0) a) b :=
  constant_abstraction_beta_of_hypotheses (StructuralTheory.empty levels) hn hΓ hA hI hb ha

theorem head_beta {g : Tm 1} (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A) (hI : Γ.JEqB levels ∅ (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (hg : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ I (g.open x) (g.open x))
    (ha : Γ.JEqB levels ∅ A a a)
    (hf : Γ.JEqB levels ∅ (.arr (B.lst a) (.wtype A B)) f f) :
    Γ.JEqB levels ∅ I (Tm.head A B I g (.sup A B a f)) (g.lst a) :=
  head_beta_of_hypotheses (StructuralTheory.empty levels) hn hΓ hA hI hB hg ha hf

theorem recChildren_constant_beta (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A) (hI : Γ.JEqB levels ∅ (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (hs : Γ.JEqB levels ∅ (Tm.wStepType A B I.wk0) s s)
    (ha : Γ.JEqB levels ∅ A a a)
    (hf : Γ.JEqB levels ∅ (.arr (B.lst a) (.wtype A B)) f f)
    (hp : Γ.JEqB levels ∅ (B.lst a) p p) :
    Γ.JEqB levels ∅ I
      (.app (Tm.recChildren A B I.wk0 s a f) p)
      (.wrec A B I.wk0 s (.app f p)) :=
  recChildren_constant_beta_of_hypotheses (StructuralTheory.empty levels) hn hΓ hA hI hB hs ha hf hp

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
