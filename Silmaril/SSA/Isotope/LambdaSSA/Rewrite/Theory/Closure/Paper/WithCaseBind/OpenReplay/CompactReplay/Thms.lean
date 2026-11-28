module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.CompactReplay.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Frames.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CompactReplay

/-! # Reflection of terminal row equality on actual compact SSA arrows -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance compactReplayThmsHasTy : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- Replay a compact compiled terminal to the quote in physical packet order. -/
theorem orderedExpr_quote {L : List (Ty Empty)} {n : Nat} (e : OrderedExpr n)
    (emits : List Bool) (pos : Position L) :
    selectedEq (e.selected emits pos)
      (selectTerminal pos (Finite.Expr.quote n e.packetEval) (readReply n) emits) :=
  CompactReplay.orderedExpr_quote e emits pos

/-- Row agreement after inverse reindexing gives an equation on the two
actual compact terminal elaborations. The typed exit and emits are shared. -/
theorem orderedExpr_eq {L : List (Ty Empty)} {n : Nat} (e f : OrderedExpr n)
    (emits : List Bool) (pos : Position L) (h : e.Agrees f) :
    selectedEq (e.selected emits pos) (f.selected emits pos) :=
  CompactReplay.orderedExpr_eq e f emits pos h

/-- Compact terminal replay at any structural reply frame, including the
extra unit field and survivor map of a retained-bit guard. -/
theorem orderedExpr_eqWith {L : List (Ty Empty)} {n : Nat} {X : Ty Empty} {frame : ReplyFrame X}
    (slots : Fin n → ReplyFrame.Slot frame) (e f : OrderedExpr n) (emits : List Bool)
    (pos : Position L) (h : e.Agrees f) :
    selectedEq (selectTerminal pos e.expr (fun j => (slots (e.order j)).term) emits)
      (selectTerminal pos f.expr (fun j => (slots (f.order j)).term) emits) :=
  CompactReplay.orderedExpr_eqWith slots e f emits pos h

/-- The compact elaboration agrees with its canonical standard-order
witness through the shared requests and retained-bit guards. -/
theorem RequestSkeleton.packed_eq_quoted {L : List (Ty Empty)} {n : Nat} (s : RequestSkeleton L n)
    (leaves : s.Leaves) : s.packed leaves = OpenReplay.packed (s.quoted leaves) :=
  CompactReplay.RequestSkeleton.packed_eq_quoted s leaves

/-- Row agreement at every terminal yields native equality of the actual
compact packed arrows, at the common request and exit interface. -/
theorem RequestSkeleton.packed_eq {L : List (Ty Empty)} {n : Nat} (s : RequestSkeleton L n)
    (l r : s.Leaves) (h : s.Agrees l r) : s.packed l = s.packed r :=
  CompactReplay.RequestSkeleton.packed_eq s l r h

/-- Recover the entire selected request and guard skeleton of an existing
tree. Identity slot orders give its literal selected compilation. -/
def presentReadTree {L : List (Ty Empty)} {n : Nat} (p : ReadTree L n) : RequestPresentation p :=
  CompactReplay.presentReadTree p

/-- Recover the skeleton and identity-order terminals of an existing
request-only selected tree, with literal equality of its selection. -/
def RequestOnly.present {L : List (Ty Empty)} {n : Nat} {p : ReadTree L n}
    (h : RequestOnly p) : RequestPresentation p :=
  CompactReplay.RequestOnly.present h

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay
