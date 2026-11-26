module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Frames.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Syntax.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FramedReplay

/-! # Extensionality and slot permutations in structural reply frames -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open Paper.WithCaseBind.SelectedTerminal (Seed)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

local instance framesThmsHasTy : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- Constructor frames detect native equality of typed regions at the same
open framed input and outward interface. -/
theorem frame_case_ext {L : List (Ty Empty)} {X : Ty Empty} (frame : ReplyFrame X)
    {p q : Region signature.Instr} (hp : HasType [X] p L) (hq : HasType [X] q L)
    (rows : ∀ {Γ : List (Ty Empty)} (v : ReplyFrame.Value Γ frame),
      Paper.Extension.Eqv Seed Γ (p.substVars (Tm.singleSubst v.elaborate.val))
        (q.substVars (Tm.singleSubst v.elaborate.val)) L) : Paper.Extension.Eqv Seed [X] p q L :=
  FramedReplay.frame_case_ext frame hp hq rows

/-- The structural projection map uses the actual request binder. -/
theorem bindSlots_term {n : Nat} {X : Ty Empty} {frame : ReplyFrame X} (slots : Fin n → ReplyFrame.Slot frame) :
    (fun j => (ReplyFrame.bindSlots slots j).term) = bindReply (fun j => (slots j).term) :=
  FramedReplay.bindSlots_term slots

/-- The framed slot map compiles to the actual guard's survivor map. -/
theorem guardSlots_term {n : Nat} {X : Ty Empty} {frame : ReplyFrame X}
    (slots : Fin (n + 1) → ReplyFrame.Slot frame) (test : Fin (n + 1)) :
    (fun j => (ReplyFrame.guardSlots slots test j).term) = guardReplies (fun j => (slots j).term) test :=
  FramedReplay.guardSlots_term slots test

theorem standardSlots_term (n : Nat) : (fun j => (ReplyFrame.standardSlots n j).term) = readReply n :=
  FramedReplay.standardSlots_term n

theorem frameSlot_discards {X : Ty Empty} {frame : ReplyFrame X} (slot : ReplyFrame.Slot frame) :
    Paper.Extension.ReturnDiscards Seed [X] slot.term.elaborate.val :=
  FramedReplay.frameSlot_discards slot

/-- Permuting the structural projections and applying the inverse to the table
preserves the selected terminal at its actual frame, prefix, and typed exit. -/
theorem selected_permute_quote_inFrame {n : Nat} {L : List (Ty Empty)} {X : Ty Empty}
    {frame : ReplyFrame X} (slots : Fin n → ReplyFrame.Slot frame) (pos : Position L)
    (emits : List Bool) (table : Finite.Table n) (order : Equiv.Perm (Fin n)) :
    selectedEq (selectTerminal pos (Finite.Expr.quote n table) (fun j => (slots j).term) emits)
      (selectTerminal pos (Finite.Expr.quote n (fun row => table (row ∘ order.symm)))
        (fun j => (slots (order j)).term) emits) :=
  FramedReplay.selected_permute_quote_inFrame slots pos emits table order

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay
