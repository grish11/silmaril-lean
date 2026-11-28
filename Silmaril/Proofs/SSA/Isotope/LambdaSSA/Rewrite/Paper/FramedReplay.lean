module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Frames.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Syntax.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.PacketCases.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.ProjectionQuote.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.RedundantTest.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Endpoint.Thms

/-! # Structural frame extensionality and native slot transport -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FramedReplay

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open Paper.WithCaseBind.SelectedTerminal (Seed)
open Paper.WithCaseBind.OpenReplay
open Paper (splitProduct)

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy
local notation "U" => (unit : Ty Empty)
local notation "E" => Paper.Extension.Eqv Seed
local notation "UnitValue" => ReplyFrame.UnitValue
local notation "FrameValue" => ReplyFrame.Value

private abbrev ConstructorSubst (Γ Δ : List (Ty Empty)) (σ : Nat → Tm signature.Instr) : Prop :=
  ∀ ⦃j D⦄, At Γ j D → Tm.BranchValue Δ (σ j) D

private theorem substType {Γ Δ : List (Ty Empty)} {σ : Nat → Tm signature.Instr}
    (h : ConstructorSubst Γ Δ σ) : Tm.Subst.HasType Γ Δ σ :=
  fun _ _ hj => (h hj).hasType

private theorem composeConstructors {Γ Δ Ξ : List (Ty Empty)} {σ υ : Nat → Tm signature.Instr}
    (hσ : ConstructorSubst Γ Δ σ) (hυ : ConstructorSubst Δ Ξ υ) :
    ConstructorSubst Γ Ξ (fun j => (σ j).subst υ) :=
  fun _ _ hj => (hσ hj).subst hυ

private theorem frame_ext_at {Γ L : List (Ty Empty)} {X : Ty Empty}
    (frame : ReplyFrame X) {i : Nat} {p q : Region signature.Instr}
    (hi : At Γ i X) (hp : HasType Γ p L) (hq : HasType Γ q L)
    (rows : ∀ {Δ : List (Ty Empty)} (v : FrameValue Δ frame) (σ : Nat → Tm signature.Instr),
      ConstructorSubst Γ Δ σ → σ i = v.elaborate.val → E Δ (p.substVars σ) (q.substVars σ) L) :
    E Γ p q L := by
  induction frame generalizing Γ i p q with
  | base =>
    have eq := rows (.base ⟨.var i, .var hi⟩) Tm.var (fun _ _ h => .var h) rfl
    simpa only [substVars_var] using eq
  | @unit X older ih =>
    apply product_case_ext hi hp hq
    have split := splitProduct_values hi
    have hOld : At (U :: X :: Γ) 1 X := rfl
    apply ih hOld (hp.substVars (substType split)) (hq.substVars (substType split))
    intro Δ v σ hσ atFocus
    let u : UnitValue Δ := ⟨σ 0, hσ (j := 0) (D := U) rfl⟩
    rw [substVars_comp, substVars_comp]
    apply rows (.unit v u) _ (composeConstructors split hσ)
    simp only [splitProduct, ↓reduceIte, Tm.subst, atFocus]
    rfl
  | @bit X older ih =>
    apply product_case_ext hi hp hq
    have split := splitProduct_values hi
    let hp' := hp.substVars (substType split)
    let hq' := hq.substVars (substType split)
    have hBit : At (Bit :: X :: Γ) 0 Bit := rfl
    apply bit_case_ext hBit hp' hq'
    intro b
    have tagged := bitBranch_values hBit b
    have hOld : At (U :: Bit :: X :: Γ) 2 X := rfl
    apply ih hOld (hp'.substVars (substType tagged)) (hq'.substVars (substType tagged))
    intro Δ v σ hσ atFocus
    let u : UnitValue Δ := ⟨σ 0, hσ (j := 0) (D := U) rfl⟩
    simp only [substVars_comp, Tm.subst_comp]
    apply rows (.bit v b u) _ (composeConstructors split (composeConstructors tagged hσ))
    rw [← Tm.subst_comp]
    cases b <;>
      simp only [splitProduct, ↓reduceIte, Tm.subst, bitBranch, Nat.one_ne_zero, replyBitTag, Bool.false_eq_true, atFocus] <;>
      rfl

theorem frame_case_ext {L : List (Ty Empty)} {X : Ty Empty} (frame : ReplyFrame X)
    {p q : Region signature.Instr} (hp : HasType [X] p L) (hq : HasType [X] q L)
    (rows : ∀ {Γ : List (Ty Empty)} (v : FrameValue Γ frame),
      E Γ (p.substVars (Tm.singleSubst v.elaborate.val))
        (q.substVars (Tm.singleSubst v.elaborate.val)) L) : E [X] p q L := by
  apply frame_ext_at frame (i := 0) rfl hp hq
  intro Γ v σ _ atFocus
  rw [Paper.SingletonReification.SingleCfg.singleton_subst hp
      (υ := Tm.singleSubst v.elaborate.val) atFocus,
    Paper.SingletonReification.SingleCfg.singleton_subst hq
      (υ := Tm.singleSubst v.elaborate.val) atFocus]
  exact rows v


theorem bindSlots_term {n : Nat} {X : Ty Empty} {frame : ReplyFrame X} (slots : Fin n → ReplyFrame.Slot frame) :
    (fun j => (ReplyFrame.bindSlots slots j).term) = bindReply (fun j => (slots j).term) := by
  funext j
  cases j using Fin.cases <;> rfl

theorem guardSlots_term {n : Nat} {X : Ty Empty} {frame : ReplyFrame X}
    (slots : Fin (n + 1) → ReplyFrame.Slot frame) (test : Fin (n + 1)) :
    (fun j => (ReplyFrame.guardSlots slots test j).term) = guardReplies (fun j => (slots j).term) test :=
  bindSlots_term (fun j => ReplyFrame.Slot.retainUnit (slots (test.succAbove j)))

theorem standardSlots_term (n : Nat) : (fun j => (ReplyFrame.standardSlots n j).term) = readReply n := by
  induction n with
  | zero => funext j; exact j.elim0
  | succ n ih =>
    change (fun j => (ReplyFrame.bindSlots (ReplyFrame.standardSlots n) j).term) =
      bindReply (readReply n)
    rw [bindSlots_term, ih]

theorem frameSlot_discards {X : Ty Empty} {frame : ReplyFrame X} (slot : ReplyFrame.Slot frame) :
    Paper.Extension.ReturnDiscards Seed [X] slot.term.elaborate.val := by
  induction slot with
  | @newest X older => exact snd_discards X Bit
  | retainUnit slot ih => exact retainSlot_discards slot.term ih
  | retainBit slot ih => exact retainSlot_discards slot.term ih

theorem selected_permute_quote_inFrame {n : Nat} {L : List (Ty Empty)} {X : Ty Empty}
    {frame : ReplyFrame X} (slots : Fin n → ReplyFrame.Slot frame) (pos : Position L)
    (emits : List Bool) (table : Finite.Table n) (order : Equiv.Perm (Fin n)) :
    selectedEq (selectTerminal pos (Finite.Expr.quote n table) (fun j => (slots j).term) emits)
      (selectTerminal pos (Finite.Expr.quote n (fun row => table (row ∘ order.symm)))
        (fun j => (slots (order j)).term) emits) := by
  let reindexed := fun row : Finite.Assignment n => table (row ∘ order.symm)
  let left := selectTerminal pos (Finite.Expr.quote n table) (fun j => (slots j).term) []
  let right := selectTerminal pos (Finite.Expr.quote n reindexed) (fun j => (slots (order j)).term) []
  have bare : selectedEq left right := by
    apply frame_case_ext frame left.elaborate.property.hasType right.elaborate.property.hasType
    intro Γ v
    have normal := quote_frameValue pos table slots v
    have reordered := quote_frameValue pos reindexed (fun j => slots (order j)) v
    have recover : ((fun j => ((slots (order j)).read v).1) ∘ order.symm) =
        (fun j => ((slots j).read v).1) := by
      funext j
      simp only [Function.comp_apply, Equiv.apply_symm_apply]
    dsimp only [reindexed] at reordered
    simp only [recover] at reordered
    exact normal.trans reordered.symm
  exact (terminal_prefix (Finite.Expr.quote n table) pos (fun j => (slots j).term) emits).trans
    ((prependEmits_congr emits bare).trans
      (terminal_prefix (Finite.Expr.quote n reindexed) pos (fun j => (slots (order j)).term) emits).symm)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FramedReplay
