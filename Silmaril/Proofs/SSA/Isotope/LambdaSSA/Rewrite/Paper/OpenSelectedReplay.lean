module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Extensional.Selected.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.Normalization.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Packed.ReplyAgreement.NativeReplay.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.ExitPacking.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Extensional.Thms

/-! # Forward replay on the open product of retained replies -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OpenSelectedReplay

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open Paper.WithCaseBind.SelectedTerminal (Seed)
open CaseTree.ReplyAgreement.NativeReplay (case_congr)
open Paper.WithCaseBind (case_return_bit)
open Paper.WithCaseBind.OpenReplay
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite (Derivable)

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

theorem newestTable_eval (n : Nat) (env : Finite.Assignment (n + 1)) :
    (newestTable n).eval env = env 0 := by
  cases h : env 0 <;> simp [Finite.Expr.eval, h]

theorem newest_eq {X : Ty Empty} {L : List (Ty Empty)} {n : Nat}
    (emits : List Bool) (pos : Position L) (slots : Fin (n + 1) → Term signature.Instr X Bit) :
    selectedEq (selectTerminal pos (.read 0) slots emits)
      (selectTerminal pos (newestTable n) slots emits) :=
  (case_return_bit Or.inr (fun e => .inl (.inl (.inr (.inl e))))
    (fun e => .inl (.inl (.inl (.inr e))))
    (emitPrefix emits (slots 0)).elaborate.property pos.typed).symm

theorem packed_congr {L : List (Ty Empty)} {n : Nat} {p q : ReadTree L n}
    (h : selectedEq p.selected q.selected) : packed p = packed q :=
  (Paper.Extension.Singleton.ofRegion_eq_iff Seed _ _).2
    (h.lsubstPost p.selected.elaborate.property q.selected.elaborate.property
      (fun _ _ hi => (packExits_valueFamily _ L hi).hasType))

theorem packed_newest_eq {L : List (Ty Empty)} {n : Nat} (emits : List Bool) (pos : Position L) :
    packed (.ret (n := n + 1) emits pos 0) = packed (.retExpr emits pos (newestTable n)) :=
  packed_congr (newest_eq emits pos (readReply (n + 1)))

theorem request_congr {L : List (Ty Empty)} {X : Ty Empty} {n : Nat}
    (slots : Fin n → Term signature.Instr X Bit) (emits : List Bool) (label bound bound' : Bool)
    {l l' r r' : ReadTree L (n + 1)}
    (hl : selectedEq (l.selectedWith (bindReply slots)) (l'.selectedWith (bindReply slots)))
    (hr : selectedEq (r.selectedWith (bindReply slots)) (r'.selectedWith (bindReply slots))) :
    selectedEq ((ReadTree.request emits label bound l r).selectedWith slots)
      ((ReadTree.request emits label bound' l' r').selectedWith slots) :=
  case_congr _ hl hr

theorem testRequest_congr {L : List (Ty Empty)} {X : Ty Empty} {n : Nat}
    (slots : Fin (n + 1) → Term signature.Instr X Bit) (emits : List Bool)
    (test : Fin (n + 1)) (label low high low' high' : Bool)
    {fl fl' fr fr' tl tl' tr tr' : ReadTree L (n + 1)}
    (hfl : selectedEq (fl.selectedWith (guardReplies slots test)) (fl'.selectedWith (guardReplies slots test)))
    (hfr : selectedEq (fr.selectedWith (guardReplies slots test)) (fr'.selectedWith (guardReplies slots test)))
    (htl : selectedEq (tl.selectedWith (guardReplies slots test)) (tl'.selectedWith (guardReplies slots test)))
    (htr : selectedEq (tr.selectedWith (guardReplies slots test)) (tr'.selectedWith (guardReplies slots test))) :
    selectedEq ((ReadTree.testRequest emits test label low high fl fr tl tr).selectedWith slots)
      ((ReadTree.testRequest emits test label low' high' fl' fr' tl' tr').selectedWith slots) :=
  case_congr _ (case_congr _ hfl hfr) (case_congr _ htl htr)


set_option backward.isDefEq.respectTransparency false in
theorem replay_selectedWith {L : List (Ty Empty)} {n : Nat} {p q : ReadTree L n} (h : Replay L p q)
    {X : Ty Empty} (slots : Fin n → Term signature.Instr X Bit) :
    selectedEq (p.selectedWith slots) (q.selectedWith slots) := by
  induction h generalizing X with
  | refl p => exact .refl (p.selectedWith slots).elaborate.property.hasType
  | symm _ ih => exact (ih slots).symm
  | trans _ _ ip iq => exact (ip slots).trans (iq slots)
  | newest emits pos => exact newest_eq emits pos slots
  | request emits label bound bound' _ _ il ir =>
    exact request_congr slots emits label bound bound' (il (bindReply slots)) (ir (bindReply slots))
  | testRequest emits test label low high low' high' _ _ _ _ ifl ifr itl itr =>
    exact testRequest_congr slots emits test label low high low' high'
      (ifl (guardReplies slots test)) (ifr (guardReplies slots test))
      (itl (guardReplies slots test)) (itr (guardReplies slots test))

theorem replay_packed {L : List (Ty Empty)} {n : Nat} {p q : ReadTree L n}
    (h : Replay L p q) : packed p = packed q :=
  packed_congr (replay_selectedWith h (readReply n))

private theorem normal_emits {L : List (Ty Empty)} {n : Nat} (emits : List Bool) (t : Finite.Tree L n) :
    (emits.foldr Finite.Tree.emit t).normal = emits.foldr Finite.Normal.emit t.normal := by
  induction emits with
  | nil => rfl
  | cons b bs ih => simp only [List.foldr, Finite.Tree.normal, ih]

theorem replay_normal {L : List (Ty Empty)} {n : Nat} {p q : ReadTree L n} (h : Replay L p q) :
    p.witnessed.normal = q.witnessed.normal := by
  induction h with
  | refl p => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ip iq => exact ip.trans iq
  | @newest n emits pos =>
    have eq : (newestTable n).eval = (Finite.Expr.read (0 : Fin (n + 1))).eval :=
      funext (newestTable_eval n)
    simp only [ReadTree.witnessed, normal_emits, Finite.Tree.normal, eq]
  | request emits label bound bound' _ _ il ir =>
    simp only [ReadTree.witnessed, normal_emits, Finite.Tree.normal, il, ir]
  | testRequest emits test label low high low' high' _ _ _ _ ifl ifr itl itr =>
    simp only [ReadTree.witnessed, normal_emits, Finite.Tree.normal, ifl, ifr, itl, itr]

theorem replay_derivable (H : Ty Empty) (L : List (Ty Empty)) {n : Nat}
    {p q : ReadTree (H :: L) n} (h : Replay (H :: L) p q) :
    Derivable false (Finite.Extensional.Selected.equation H L p q) := by
  apply Finite.Extensional.derive_normal H L
  intro env
  exact congrArg (fun t => Finite.Extensional.specialize t env) (replay_normal h)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OpenSelectedReplay
