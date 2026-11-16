module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Head.Defs
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite.Examples

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

private theorem closed_wk0 (I : Tm 0) : I.wk0 = I.castLE (Nat.zero_le 1) :=
  Tm.wkn_past I 0 (Nat.le_refl 0)

private theorem stepType_constant (A I : Tm 0) (B : Tm 1) :
    Tm.wStepType A B I.wk0 =
      .pi A (.arr (.arr B ((.wtype A B : Tm 0).castLE (by decide)))
        (.arr (.arr B (I.castLE (by decide))) (I.castLE (by decide)))) := by
  rw [closed_wk0 I]
  simp only [Tm.wStepType, Tm.bsubst_closed_castLE, single_shift,
    Tm.arr, Tm.wk0, Tm.wkn, Tm.closed_castLE_wkn]

private theorem arrow_open (A B : Tm 1) (x : String) :
    (Tm.arr A B).open x = Tm.arr (A.open x) (B.open x) := by
  simp only [Tm.arr, Tm.open, Tm.wk0, Tm.open_wkn B x 0 (Nat.zero_le _)]

private theorem step_open (A I : Tm 0) (B g : Tm 1) (x : String) :
    ((.abs (.arr B ((.wtype A B : Tm 0).castLE (by decide)))
      ((Tm.abs (.arr B (I.castLE (by decide))) g.wk0).wk0) : Tm 1).open x) =
      .abs (.arr (B.open x) (.wtype A B))
        ((Tm.abs (.arr (B.open x) I) (g.open x).wk0).wk0) := by
  simp only [Tm.open, arrow_open, Tm.closed_castLE_open, Tm.castLE_refl,
    Tm.wk0, Tm.open_wkn _ x 0 (Nat.zero_le _)]

theorem headStep_typing_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hh : HypothesisTransport levels H H) {Γ : Ctx} {A I : Tm 0} {B g : Tm 1}
    {L : Finset String} (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hI : Γ.JEqB levels H (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hg : ∀ x ∉ L, (Γ.cons x A).JEqB levels H I (g.open x) (g.open x)) :
    Γ.JEqB levels H (Tm.wStepType A B I.wk0)
      (Tm.headStep A B I g) (Tm.headStep A B I g) := by
  have hW : Γ.JEqB levels H (.univ n) (.wtype A B) (.wtype A B) := .wtype hn hA hB
  have hlocal : ∀ x ∉ L ∪ Γ.dv,
      (Γ.cons x A).JEqB levels H (.univ n)
        (.arr (.arr (B.open x) (.wtype A B)) (.arr (.arr (B.open x) I) I))
        (.arr (.arr (B.open x) (.wtype A B)) (.arr (.arr (B.open x) I) I)) ∧
      (Γ.cons x A).JEqB levels H
        (.arr (.arr (B.open x) (.wtype A B)) (.arr (.arr (B.open x) I) I))
        (.abs (.arr (B.open x) (.wtype A B))
          ((Tm.abs (.arr (B.open x) I) (g.open x).wk0).wk0))
        (.abs (.arr (B.open x) (.wtype A B))
          ((Tm.abs (.arr (B.open x) I) (g.open x).wk0).wk0)) := by
    intro x hx
    have hxL : x ∉ L := fun h => hx (Finset.mem_union_left _ h)
    have hxΓ : x ∉ Γ.dv := fun h => hx (Finset.mem_union_right _ h)
    have hctx : (Γ.cons x A).JEqB levels H .unit .star .star :=
      .cons_ok hn hΓ hxΓ hA
    have hI' : (Γ.cons x A).JEqB levels H (.univ n) I I :=
      hΓ.weaken_cons_of_hypotheses hh hxΓ hn hA hI
    have hW' : (Γ.cons x A).JEqB levels H (.univ n) (.wtype A B) (.wtype A B) :=
      hΓ.weaken_cons_of_hypotheses hh hxΓ hn hA hW
    have hF := Ctx.JEqB.arrow_formation_of_hypotheses hh hn hctx (hB x hxL) hW'
    have hR := Ctx.JEqB.arrow_formation_of_hypotheses hh hn hctx (hB x hxL) hI'
    have hRI := Ctx.JEqB.arrow_formation_of_hypotheses hh hn hctx hR hI'
    have hinner := Ctx.JEqB.constant_abstraction_of_hypotheses hh hn hctx hR hI' (hg x hxL)
    exact ⟨Ctx.JEqB.arrow_formation_of_hypotheses hh hn hctx hF hRI,
      Ctx.JEqB.constant_abstraction_of_hypotheses hh hn hctx hF hRI hinner⟩
  rw [stepType_constant]
  unfold Tm.headStep
  apply Ctx.JEqB.abs (L := L ∪ Γ.dv) hn hA
  · intro x hx
    simpa only [arrow_open, Tm.closed_castLE_open, Tm.castLE_refl] using (hlocal x hx).1
  · intro x hx
    simpa only [step_open, arrow_open, Tm.closed_castLE_open, Tm.castLE_refl] using (hlocal x hx).2

theorem head_typing_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hh : HypothesisTransport levels H H) {Γ : Ctx} {A I t : Tm 0} {B g : Tm 1}
    {L : Finset String} (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hI : Γ.JEqB levels H (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hg : ∀ x ∉ L, (Γ.cons x A).JEqB levels H I (g.open x) (g.open x))
    (ht : Γ.JEqB levels H (.wtype A B) t t) :
    Γ.JEqB levels H I (Tm.head A B I g t) (Tm.head A B I g t) := by
  have hC : ∀ x ∉ L ∪ Γ.dv, (Γ.cons x (.wtype A B)).JEqB levels H (.univ n)
      (I.wk0.open x) (I.wk0.open x) := by
    intro x hx
    exact Ctx.JEqB.constant_family_of_hypotheses hh hn hΓ (.wtype hn hA hB) hI x
      (fun h => hx (Finset.mem_union_right _ h))
  simpa only [Tm.head, Tm.closed_wk0_lst] using Ctx.JEqB.wrec hn hn hA
    (fun x hx => hB x (fun h => hx (Finset.mem_union_left _ h))) hC
    (headStep_typing_of_hypotheses hh hn hΓ hA hI hB hg) ht

theorem headStep_typing {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A I : Tm 0} {B g : Tm 1}
    {L : Finset String} (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A) (hI : Γ.JEqB levels ∅ (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (hg : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ I (g.open x) (g.open x)) :
    Γ.JEqB levels ∅ (Tm.wStepType A B I.wk0)
      (Tm.headStep A B I g) (Tm.headStep A B I g) :=
  headStep_typing_of_hypotheses (HypothesisTransport.empty levels ∅) hn hΓ hA hI hB hg

theorem head_typing {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A I t : Tm 0} {B g : Tm 1}
    {L : Finset String} (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A) (hI : Γ.JEqB levels ∅ (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (hg : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ I (g.open x) (g.open x))
    (ht : Γ.JEqB levels ∅ (.wtype A B) t t) :
    Γ.JEqB levels ∅ I (Tm.head A B I g t) (Tm.head A B I g t) :=
  head_typing_of_hypotheses (HypothesisTransport.empty levels ∅) hn hΓ hA hI hB hg ht

/-- Reuse the existing closed leaf to instantiate the eliminator at count one. -/
theorem head_leaf_typing : Ctx.JEqB 1 ∅ .nil .unit
    (Tm.head .unit .empty .unit .star Examples.leaf)
    (Tm.head .unit .empty .unit .star Examples.leaf) := by
  have hctx (x : String) : (Ctx.nil.cons x .unit).JEqB 1 ∅ .unit .star .star :=
    .cons_ok (n := 0) (by decide) .nil_ok (by simp [Ctx.dv]) (.unit (by decide) .nil_ok)
  have hB : ∀ x ∉ (∅ : Finset String), (Ctx.nil.cons x .unit).JEqB 1 ∅ (.univ 0)
      ((.empty : Tm 1).open x) ((.empty : Tm 1).open x) := by
    intro x _
    simpa only [Tm.open] using Ctx.JEqB.empty (n := 0) (by decide) (hctx x)
  have hg : ∀ x ∉ (∅ : Finset String), (Ctx.nil.cons x .unit).JEqB 1 ∅ .unit
      ((.star : Tm 1).open x) ((.star : Tm 1).open x) := by
    intro x _
    simpa only [Tm.open] using hctx x
  exact head_typing (n := 0) (by decide) .nil_ok (.unit (by decide) .nil_ok)
    (.unit (by decide) .nil_ok) hB hg
    (by simpa only [Examples.Leaf] using Finite.Examples.leaf_closed)

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
