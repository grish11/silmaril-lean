module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Comparison.Compact.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.ComputedTable.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Frames.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.RedundantTest.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Packed.ReplyAgreement.NativeReplay.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.Thms

/-! # Native replay of recognized compact table reductions -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CompactTerminalReplay

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open CaseTree.ReplyAgreement.NativeReplay (case_congr)
open Paper.WithCaseBind.OpenReplay
open Paper.WithCaseBind.OpenReplay.CompactTerminal
open Paper.WithCaseBind.SelectedTerminal (Seed)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

private def atomValue {Γ : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X}
    (v : ReplyFrame.Value Γ frame) : Atom frame → Bool
  | .inl tag => tag
  | .inr slot => (slot.read v).1

private abbrev Valid {Γ : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X}
    (v : ReplyFrame.Value Γ frame) (known : Known frame) : Prop :=
  ∀ slot tag, known slot = some tag → (slot.read v).1 = tag

private theorem remember_valid {Γ : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X}
    {v : ReplyFrame.Value Γ frame} {known : Known frame} (valid : Valid v known)
    (slot : ReplyFrame.Slot frame) (tag : Bool) (tagged : (slot.read v).1 = tag) :
    Valid v (remember known slot tag) := by
  intro query b remembered
  by_cases same : query = slot
  · subst query
    simp [remember] at remembered
    exact tagged.trans remembered
  · apply valid query b
    simpa [remember, same] using remembered

private theorem resolve_value {Γ : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X}
    {v : ReplyFrame.Value Γ frame} {known : Known frame} (valid : Valid v known)
    (val : Atom frame) : atomValue v (resolve known val) = atomValue v val := by
  cases val with
  | inl b => rfl
  | inr slot =>
    cases h : known slot with
    | none => simp [resolve, h]
    | some tag => simpa [resolve, h, atomValue] using (valid slot tag h).symm

private theorem check_value {Γ : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X}
    (v : ReplyFrame.Value Γ frame) {n : Nat} (e : Finite.Expr n) (slots : Fin n → ReplyFrame.Slot frame)
    (known : Known frame) (target : Atom frame) (valid : Valid v known)
    (passed : check e slots known target = true) :
    e.eval (fun j => ((slots j).read v).1) = atomValue v target := by
  induction e generalizing known with
  | literal b =>
    simp only [check, decide_eq_true_eq] at passed
    exact (congrArg (atomValue v) passed).symm.trans (resolve_value valid target)
  | read i =>
    simp only [check, decide_eq_true_eq] at passed
    exact (resolve_value valid (.inr (slots i))).symm.trans
      ((congrArg (atomValue v) passed).symm.trans (resolve_value valid target))
  | split low high il ih =>
    cases saved : known (slots 0) with
    | none =>
      simp only [check, saved, Bool.and_eq_true] at passed
      cases tag : ((slots 0).read v).1
      · simpa [Finite.Expr.eval, tag] using!
          il _ _ (remember_valid valid (slots 0) false tag) passed.1
      · simpa [Finite.Expr.eval, tag] using!
          ih _ _ (remember_valid valid (slots 0) true tag) passed.2
    | some b =>
      have tag := valid (slots 0) b saved
      cases b
      · simp only [check, saved] at passed
        simpa [Finite.Expr.eval, tag] using! il _ _ valid passed
      · simp only [check, saved] at passed
        simpa [Finite.Expr.eval, tag] using! ih _ _ valid passed

theorem selected_of_frame_row {Γ : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X}
    {L : List (Ty Empty)} {n m : Nat} (e : Finite.Expr n) (out : Finite.Expr m)
    (slots : Fin n → ReplyFrame.Slot frame) (otherSlots : Fin m → ReplyFrame.Slot frame)
    (pos : Position L) (emits : List Bool) (v : ReplyFrame.Value Γ frame)
    (row : e.eval (fun j => ((slots j).read v).1) = out.eval (fun j => ((otherSlots j).read v).1)) :
    Paper.Extension.Eqv Seed Γ
      ((selectTerminal pos e (fun j => (slots j).term) emits).elaborate.val.substVars
        (Tm.singleSubst v.elaborate.val))
      ((selectTerminal pos out (fun j => (otherSlots j).term) emits).elaborate.val.substVars
        (Tm.singleSubst v.elaborate.val)) L := by
  let σ := Tm.singleSubst v.elaborate.val
  have typed : ∀ ⦃i D⦄, At [X] i D → Tm.BranchValue Γ (σ i) D := by
    intro i D hi
    cases i with
    | zero => cases Option.some.inj hi; exact v.elaborate.property
    | succ i => simp [At] at hi
  let terms := fun j => (slots j).term
  let otherTerms := fun j => (otherSlots j).term
  have left := (terminal_prefix e pos terms emits).substVars typed
  have right := (terminal_prefix out pos otherTerms emits).substVars typed
  rw [prependEmits_subst] at left right
  have lq := (quote_eval_selected e pos terms [] (fun j => frameSlot_discards (slots j))).symm.substVars typed
  have rq := (quote_eval_selected out pos otherTerms [] (fun j => frameSlot_discards (otherSlots j))).substVars typed
  have l := quote_frameValue pos e.eval slots v
  have r := quote_frameValue pos out.eval otherSlots v
  rw [row] at l
  exact left.trans ((prependEmits_congr emits (lq.trans (l.trans (r.symm.trans rq)))).trans right.symm)

theorem selected_of_frame_rows {X : Ty Empty} {frame : ReplyFrame X} {L : List (Ty Empty)} {n m : Nat}
    (e : Finite.Expr n) (out : Finite.Expr m)
    (slots : Fin n → ReplyFrame.Slot frame) (otherSlots : Fin m → ReplyFrame.Slot frame)
    (pos : Position L) (emits : List Bool)
    (rows : ∀ {Γ : List (Ty Empty)} (v : ReplyFrame.Value Γ frame),
      e.eval (fun j => ((slots j).read v).1) = out.eval (fun j => ((otherSlots j).read v).1)) :
    selectedEq (selectTerminal pos e (fun j => (slots j).term) emits)
      (selectTerminal pos out (fun j => (otherSlots j).term) emits) :=
  frame_case_ext frame (selectTerminal pos e (fun j => (slots j).term) emits).elaborate.property.hasType
    (selectTerminal pos out (fun j => (otherSlots j).term) emits).elaborate.property.hasType
    (fun v => selected_of_frame_row e out slots otherSlots pos emits v (rows v))

theorem selected_of_check {X : Ty Empty} {frame : ReplyFrame X} {L : List (Ty Empty)} {n : Nat}
    (e : Finite.Expr n) (out : Terminal n) (slots : Fin n → ReplyFrame.Slot frame)
    (pos : Position L) (emits : List Bool)
    (passed : check e slots (fun _ => none) (out.atom slots) = true) :
    selectedEq (selectTerminal pos e (fun j => (slots j).term) emits)
      (selectTerminal pos out.expr (fun j => (slots j).term) emits) := by
  apply selected_of_frame_rows
  intro Γ v
  have row := check_value v e slots (fun _ => none) (out.atom slots) (by intro _ _ h; cases h) passed
  exact row.trans (by cases out <;> rfl)

theorem selected_of_infer {X : Ty Empty} {frame : ReplyFrame X} {L : List (Ty Empty)} {n : Nat}
    (e : Finite.Expr n) (out : Terminal n) (slots : Fin n → ReplyFrame.Slot frame)
    (pos : Position L) (emits : List Bool) (found : infer? e slots = some out) :
    selectedEq (selectTerminal pos e (fun j => (slots j).term) emits)
      (selectTerminal pos out.expr (fun j => (slots j).term) emits) := by
  unfold infer? at found
  have passed := List.find?_some found
  exact selected_of_check e out slots pos emits passed

set_option backward.isDefEq.respectTransparency false in
theorem reduceTree_selected {X : Ty Empty} {frame : ReplyFrame X} {L : List (Ty Empty)} {n : Nat}
    (p : ReadTree L n) (slots : Fin n → ReplyFrame.Slot frame) :
    selectedEq (p.selectedWith (fun j => (slots j).term))
      ((reduceTree p slots).selectedWith (fun j => (slots j).term)) := by
  induction p generalizing X with
  | ret =>
    exact .refl (ReadTree.selectedWith _ (fun j => (slots j).term)).elaborate.property.hasType
  | retExpr emits pos e =>
    cases h : infer? e slots with
    | none =>
      simp only [reduceTree, h]
      exact .refl (selectTerminal pos e (fun j => (slots j).term) emits).elaborate.property.hasType
    | some result =>
      have localEq := selected_of_infer e result slots pos emits h
      cases result <;> simpa only [reduceTree, h, ReadTree.selectedWith, Terminal.expr] using localEq
  | request emits label bound l r il ir =>
    have left := il (ReplyFrame.bindSlots slots)
    have right := ir (ReplyFrame.bindSlots slots)
    rw [bindSlots_term] at left right
    exact case_congr _ left right
  | testRequest emits test low lowBound highBound fl fr tl tr ifl ifr itl itr =>
    have left := ifl (ReplyFrame.guardSlots slots test)
    have right := ifr (ReplyFrame.guardSlots slots test)
    have left' := itl (ReplyFrame.guardSlots slots test)
    have right' := itr (ReplyFrame.guardSlots slots test)
    rw [guardSlots_term] at left right left' right'
    exact case_congr _ (case_congr _ left right) (case_congr _ left' right')

set_option backward.isDefEq.respectTransparency false in
theorem packed_eq_reduceCompact {X : Ty Empty} {L : List (Ty Empty)} (p : SelectedAt X L) :
    p.packedSource = p.reduceCompact.packedSource := by
  let slots := fun j => ReplyFrame.Slot.retainUnit (p.slots j)
  have eq : selectedEq p.source p.reduceCompact.source :=
    case_congr _ (reduceTree_selected p.split.onFalse slots) (reduceTree_selected p.split.onTrue slots)
  exact (Paper.Extension.Singleton.ofRegion_eq_iff Seed _ _).2
    (eq.lsubstPost p.source.elaborate.property p.reduceCompact.source.elaborate.property
      (fun _ _ hi => (packExits_valueFamily _ L hi).hasType))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CompactTerminalReplay
