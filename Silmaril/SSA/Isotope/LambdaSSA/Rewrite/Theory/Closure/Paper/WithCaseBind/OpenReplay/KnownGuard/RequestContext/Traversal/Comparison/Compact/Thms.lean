module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Comparison.Compact.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Comparison.CanonicalLive.Admission.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CompactTerminalReplay

/-! # Checked compact-terminal reduction and comparison -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.SelectedTerminal (Seed)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- Replay at a single constructor packet, with its original typed
payloads and the shared emit prefix. -/
theorem CompactTerminal.selected_of_frame_row {Γ : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X}
    {L : List (Ty Empty)} {n m : Nat} (e : Finite.Expr n) (out : Finite.Expr m)
    (slots : Fin n → ReplyFrame.Slot frame) (otherSlots : Fin m → ReplyFrame.Slot frame)
    (pos : Position L) (emits : List Bool) (v : ReplyFrame.Value Γ frame)
    (row : e.eval (fun j => ((slots j).read v).1) = out.eval (fun j => ((otherSlots j).read v).1)) :
    Paper.Extension.Eqv Seed Γ
      ((selectTerminal pos e (fun j => (slots j).term) emits).elaborate.val.substVars
        (Tm.singleSubst v.elaborate.val))
      ((selectTerminal pos out (fun j => (otherSlots j).term) emits).elaborate.val.substVars
        (Tm.singleSubst v.elaborate.val)) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CompactTerminalReplay.selected_of_frame_row
    e out slots otherSlots pos emits v row

/-- Constructor rows replay at two arbitrary exact slot maps on the same
frame, preserving the shared emit prefix and typed exit. -/
theorem CompactTerminal.selected_of_frame_rows {X : Ty Empty} {frame : ReplyFrame X} {L : List (Ty Empty)}
    {n m : Nat} (e : Finite.Expr n) (out : Finite.Expr m)
    (slots : Fin n → ReplyFrame.Slot frame) (otherSlots : Fin m → ReplyFrame.Slot frame)
    (pos : Position L) (emits : List Bool)
    (rows : ∀ {Γ : List (Ty Empty)} (v : ReplyFrame.Value Γ frame),
      e.eval (fun j => ((slots j).read v).1) = out.eval (fun j => ((otherSlots j).read v).1)) :
    selectedEq (selectTerminal pos e (fun j => (slots j).term) emits)
      (selectTerminal pos out (fun j => (otherSlots j).term) emits) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CompactTerminalReplay.selected_of_frame_rows
    e out slots otherSlots pos emits rows

/-- A recognized compact terminal reduces natively at its original framed
input, ordered emit prefix, and typed exit. -/
theorem CompactTerminal.selected_of_infer {X : Ty Empty} {frame : ReplyFrame X}
    {L : List (Ty Empty)} {n : Nat} (e : Finite.Expr n) (out : CompactTerminal.Terminal n)
    (slots : Fin n → ReplyFrame.Slot frame) (pos : Position L) (emits : List Bool)
    (found : CompactTerminal.infer? e slots = some out) :
    selectedEq (selectTerminal pos e (fun j => (slots j).term) emits)
      (selectTerminal pos out.expr (fun j => (slots j).term) emits) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CompactTerminalReplay.selected_of_infer e out slots pos emits found

/-- Replay the terminal reductions on the actual original packed arrow. -/
theorem SelectedAt.packed_eq_reduceCompact {X : Ty Empty} {L : List (Ty Empty)} (p : SelectedAt X L) :
    p.packedSource = p.reduceCompact.packedSource :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CompactTerminalReplay.packed_eq_reduceCompact p

namespace CanonicalLive

/-- Comparison of the original endpoints, using exact canonical admission
on both reduced programs for a distinguishing verdict. -/
inductive CompactVerdict {L : List (Ty Empty)} {n : Nat} (p q : SelectedAt (replyContext n) L) where
  | equal (proof : p.packedSource = q.packedSource)
  | different (left : Admission p.reduceCompact.projectionCanonical)
      (right : Admission q.reduceCompact.projectionCanonical)
      (input : Finite.Assignment n) (proof : observations p input ≠ observations q input)
  | unknown

/-- Run the existing comparison after native compact-terminal reduction. -/
@[expose] def compareCompact {L : List (Ty Empty)} {n : Nat} (p q : SelectedAt (replyContext n) L) :
    CompactVerdict p q :=
  match compareSelected p.reduceCompact q.reduceCompact with
  | .equal equation => .equal (p.packed_eq_reduceCompact.trans (equation.trans q.packed_eq_reduceCompact.symm))
  | .different left right input different => .different left right input (by
    simpa only [observations, p.packed_eq_reduceCompact, q.packed_eq_reduceCompact] using different)
  | .unknown => .unknown

end CanonicalLive

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay
