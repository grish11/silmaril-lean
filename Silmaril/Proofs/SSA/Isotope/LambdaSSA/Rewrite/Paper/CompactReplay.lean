module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.CompactReplay.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Frames.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.AdjacentSwap.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.ComputedTable.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Frames.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Packed.ReplyAgreement.NativeReplay.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.Thms

/-! # Native replay for compact terminals in independent slot orders -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CompactReplay

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region CategoryTheory
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.SelectedTerminal (Seed)
open Paper.WithCaseBind.OpenReplay
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

private theorem pack_selectedEq {L : List (Ty Empty)} {n : Nat}
    {l r : CaseTree signature.Instr (replyContext n) L} (h : selectedEq l r) :
    Paper.Extension.Singleton.ofRegion Seed l.elaborate.property.packExits =
      Paper.Extension.Singleton.ofRegion Seed r.elaborate.property.packExits :=
  (Paper.Extension.Singleton.ofRegion_eq_iff Seed _ _).2
    (h.lsubstPost l.elaborate.property r.elaborate.property
      (fun _ _ hi => (packExits_valueFamily _ L hi).hasType))

theorem orderedExpr_quote {L : List (Ty Empty)} {n : Nat} (e : OrderedExpr n)
    (emits : List Bool) (pos : Position L) :
    selectedEq (e.selected emits pos)
      (selectTerminal pos (Finite.Expr.quote n e.packetEval) (readReply n) emits) := by
  have recover : (fun row : Finite.Assignment n => e.packetEval (row ∘ e.order.symm)) = e.expr.eval := by
    funext row
    have eta : (row ∘ e.order.symm) ∘ e.order = row := by
      funext j
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
    exact congrArg e.expr.eval eta
  have perm := selected_permute_quote pos emits e.packetEval e.order
  rw [recover] at perm
  exact (quote_eval_selected e.expr pos (readReply n ∘ e.order) emits
    (fun j => readReply_discards n (e.order j))).symm.trans perm.symm

theorem orderedExpr_quoteWith {L : List (Ty Empty)} {n : Nat} {X : Ty Empty} {frame : ReplyFrame X}
    (slots : Fin n → ReplyFrame.Slot frame) (e : OrderedExpr n) (emits : List Bool) (pos : Position L) :
    selectedEq (selectTerminal pos e.expr (fun j => (slots (e.order j)).term) emits)
      (selectTerminal pos (Finite.Expr.quote n e.packetEval) (fun j => (slots j).term) emits) := by
  have recover : (fun row : Finite.Assignment n => e.packetEval (row ∘ e.order.symm)) = e.expr.eval := by
    funext row
    have eta : (row ∘ e.order.symm) ∘ e.order = row := by
      funext j
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
    exact congrArg e.expr.eval eta
  have perm := selected_permute_quote_inFrame slots pos emits e.packetEval e.order
  rw [recover] at perm
  exact (quote_eval_selected e.expr pos (fun j => (slots (e.order j)).term) emits
    (fun j => frameSlot_discards (slots (e.order j)))).symm.trans perm.symm

private theorem agreed_packetEval {n : Nat} {e f : OrderedExpr n} (h : e.Agrees f) :
    e.packetEval = f.packetEval := by
  funext row
  have eta : ((row ∘ e.order) ∘ e.order.symm) ∘ f.order = row ∘ f.order := by
    funext j
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  exact (h (row ∘ e.order)).trans (congrArg f.expr.eval eta)

theorem orderedExpr_eq {L : List (Ty Empty)} {n : Nat} (e f : OrderedExpr n)
    (emits : List Bool) (pos : Position L) (h : e.Agrees f) :
    selectedEq (e.selected emits pos) (f.selected emits pos) := by
  have rhs := orderedExpr_quote f emits pos
  rw [← agreed_packetEval h] at rhs
  exact (orderedExpr_quote e emits pos).trans rhs.symm

theorem orderedExpr_eqWith {L : List (Ty Empty)} {n : Nat} {X : Ty Empty} {frame : ReplyFrame X}
    (slots : Fin n → ReplyFrame.Slot frame) (e f : OrderedExpr n) (emits : List Bool)
    (pos : Position L) (h : e.Agrees f) :
    selectedEq (selectTerminal pos e.expr (fun j => (slots (e.order j)).term) emits)
      (selectTerminal pos f.expr (fun j => (slots (f.order j)).term) emits) := by
  have rhs := orderedExpr_quoteWith slots f emits pos
  rw [← agreed_packetEval h] at rhs
  exact (orderedExpr_quoteWith slots e emits pos).trans rhs.symm

set_option backward.isDefEq.respectTransparency false in
private theorem RequestSkeleton.selected_eq_quotedWith {L : List (Ty Empty)} {n : Nat}
    (s : RequestSkeleton L n) (leaves : s.Leaves) {X : Ty Empty} {frame : ReplyFrame X}
    (slots : Fin n → ReplyFrame.Slot frame) :
    selectedEq (s.selectedWith leaves (fun j => (slots j).term))
      ((s.quoted leaves).selectedWith (fun j => (slots j).term)) := by
  induction s generalizing X with
  | ret emits pos => exact orderedExpr_quoteWith slots leaves emits pos
  | request emits label left right il ir =>
    simp only [RequestSkeleton.quoted, RequestSkeleton.selectedWith, ReadTree.selectedWith]
    rw [← bindSlots_term slots]
    exact NativeReplay.case_congr (emitPrefix emits (.call (show signature.Instr from Op.ask label) .unit))
      (il leaves.1 (ReplyFrame.bindSlots slots)) (ir leaves.2 (ReplyFrame.bindSlots slots))
  | testRequest emits test low fl fr tl tr ifl ifr itl itr =>
    simp only [RequestSkeleton.quoted, RequestSkeleton.selectedWith, ReadTree.selectedWith]
    rw [← guardSlots_term slots test]
    let next := ReplyFrame.guardSlots slots test
    have nextTerms : bindReply (fun i : Fin _ => retainSlot (A := unit) (slots (test.succAbove i)).term) =
        (fun j => (next j).term) := (guardSlots_term slots test).symm
    rw [nextTerms]
    apply NativeReplay.case_congr (emitPrefix emits (slots test).term)
    · exact NativeReplay.case_congr (emitPrefix [] (.call (show signature.Instr from Op.ask low) .unit))
        (ifl leaves.1 next) (ifr leaves.2.1 next)
    · exact NativeReplay.case_congr (emitPrefix [] (.call (show signature.Instr from Op.ask (!low)) .unit))
        (itl leaves.2.2.1 next) (itr leaves.2.2.2 next)

theorem RequestSkeleton.selected_eq_quoted {L : List (Ty Empty)} {n : Nat} (s : RequestSkeleton L n)
    (leaves : s.Leaves) : selectedEq (s.selected leaves) (s.quoted leaves).selected := by
  unfold RequestSkeleton.selected ReadTree.selected
  rw [← standardSlots_term n]
  exact RequestSkeleton.selected_eq_quotedWith s leaves (ReplyFrame.standardSlots n)

theorem RequestSkeleton.packed_eq_quoted {L : List (Ty Empty)} {n : Nat} (s : RequestSkeleton L n)
    (leaves : s.Leaves) : s.packed leaves = Paper.WithCaseBind.OpenReplay.packed (s.quoted leaves) :=
  pack_selectedEq (RequestSkeleton.selected_eq_quoted s leaves)

private theorem RequestSkeleton.quoted_congr {L : List (Ty Empty)} {n : Nat} (s : RequestSkeleton L n)
    (l r : s.Leaves) (h : s.Agrees l r) : s.quoted l = s.quoted r := by
  induction s with
  | @ret n emits pos =>
    exact congrArg (fun t => ReadTree.retExpr emits pos (Finite.Expr.quote n t)) (agreed_packetEval h)
  | request emits label left right il ir =>
    exact congrArg₂ (ReadTree.request emits label false) (il _ _ h.1) (ir _ _ h.2)

  | testRequest emits test low fl fr tl tr ifl ifr itl itr =>
    rw [RequestSkeleton.quoted, RequestSkeleton.quoted,
      ifl _ _ h.1, ifr _ _ h.2.1, itl _ _ h.2.2.1, itr _ _ h.2.2.2]

theorem RequestSkeleton.packed_eq {L : List (Ty Empty)} {n : Nat} (s : RequestSkeleton L n)
    (l r : s.Leaves) (h : s.Agrees l r) : s.packed l = s.packed r :=
  (RequestSkeleton.packed_eq_quoted s l).trans
    ((congrArg Paper.WithCaseBind.OpenReplay.packed (RequestSkeleton.quoted_congr s l r h)).trans
      (RequestSkeleton.packed_eq_quoted s r).symm)

private structure FullPresentation {L : List (Ty Empty)} {n : Nat} (p : ReadTree L n) where
  skeleton : RequestSkeleton L n
  leaves : skeleton.Leaves
  compiles {X : Ty Empty} (slots : Fin n → Term signature.Instr X Bit) :
    skeleton.selectedWith leaves slots = p.selectedWith slots

private def presentWith {L : List (Ty Empty)} : {n : Nat} → (p : ReadTree L n) → FullPresentation p
  | n, .ret emits pos i => ⟨.ret emits pos, ⟨.read i, Equiv.refl (Fin n)⟩, fun _ => rfl⟩
  | n, .retExpr emits pos e => ⟨.ret emits pos, ⟨e, Equiv.refl (Fin n)⟩, fun _ => rfl⟩
  | _, .request emits label _ l r =>
    let left := presentWith l
    let right := presentWith r
    ⟨.request emits label left.skeleton right.skeleton, (left.leaves, right.leaves), fun slots =>
      congrArg₂ (selectRequest emits label) (left.compiles (bindReply slots)) (right.compiles (bindReply slots))⟩
  | _, .testRequest emits test low _ _ fl fr tl tr =>
    let falseLeft := presentWith fl
    let falseRight := presentWith fr
    let trueLeft := presentWith tl
    let trueRight := presentWith tr
    ⟨.testRequest emits test low falseLeft.skeleton falseRight.skeleton trueLeft.skeleton trueRight.skeleton,
      (falseLeft.leaves, falseRight.leaves, trueLeft.leaves, trueRight.leaves), fun slots => by
        simp only [RequestSkeleton.selectedWith, ReadTree.selectedWith,
          falseLeft.compiles, falseRight.compiles, trueLeft.compiles, trueRight.compiles]⟩

def presentReadTree {L : List (Ty Empty)} {n : Nat} (p : ReadTree L n) : RequestPresentation p :=
  let data := presentWith p
  ⟨data.skeleton, data.leaves, data.compiles (readReply n)⟩

def RequestOnly.present {L : List (Ty Empty)} {n : Nat} {p : ReadTree L n}
    (_h : RequestOnly p) : RequestPresentation p :=
  presentReadTree p

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CompactReplay
