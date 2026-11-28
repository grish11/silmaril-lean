module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Extensional.Selected.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OpenSelectedReplay

/-! # Assignment-respecting replay in the opt-in case-bind quotient -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite (Derivable)

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- The table reads the same slot at every assignment. -/
theorem newestTable_eval (n : Nat) (env : Finite.Assignment (n + 1)) :
    (newestTable n).eval env = env 0 :=
  OpenSelectedReplay.newestTable_eval n env

/-- A single reconstructing test can replace the newest read under any
selected slot map, with the same emit prefix and typed exit. -/
theorem newest_eq {X : Ty Empty} {L : List (Ty Empty)} {n : Nat}
    (emits : List Bool) (pos : Position L) (slots : Fin (n + 1) → Term signature.Instr X Bit) :
    selectedEq (selectTerminal pos (.read 0) slots emits)
      (selectTerminal pos (newestTable n) slots emits) :=
  OpenSelectedReplay.newest_eq emits pos slots

/-- Guarded representative equality transports through outward tag packing. -/
theorem packed_congr {L : List (Ty Empty)} {n : Nat} {p q : ReadTree L n}
    (h : selectedEq p.selected q.selected) : packed p = packed q :=
  OpenSelectedReplay.packed_congr h

/-- The read/table generator gives equal actual open singleton arrows. -/
theorem packed_newest_eq {L : List (Ty Empty)} {n : Nat} (emits : List Bool) (pos : Position L) :
    packed (.ret (n := n + 1) emits pos 0) = packed (.retExpr emits pos (newestTable n)) :=
  OpenSelectedReplay.packed_newest_eq emits pos

/-- Replay the two arms under the request's shared reply extension. -/
theorem request_congr {L : List (Ty Empty)} {X : Ty Empty} {n : Nat}
    (slots : Fin n → Term signature.Instr X Bit) (emits : List Bool) (label bound bound' : Bool)
    {l l' r r' : ReadTree L (n + 1)}
    (hl : selectedEq (l.selectedWith (bindReply slots)) (l'.selectedWith (bindReply slots)))
    (hr : selectedEq (r.selectedWith (bindReply slots)) (r'.selectedWith (bindReply slots))) :
    selectedEq ((ReadTree.request emits label bound l r).selectedWith slots)
      ((ReadTree.request emits label bound' l' r').selectedWith slots) :=
  OpenSelectedReplay.request_congr slots emits label bound bound' hl hr

/-- Replay the four arms under the guard's shared slot deletion and reply extension. -/
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
  OpenSelectedReplay.testRequest_congr slots emits test label low high low' high' hfl hfr htl htr

/-- Replay the generated native fragment at the full retained reply product. -/
theorem replay_packed {L : List (Ty Empty)} {n : Nat} {p q : ReadTree L n}
    (h : Replay L p q) : packed p = packed q :=
  OpenSelectedReplay.replay_packed h

/-- The witnessed normal forms agree before assignment specialization. -/
theorem replay_normal {L : List (Ty Empty)} {n : Nat} {p q : ReadTree L n} (h : Replay L p q) :
    p.witnessed.normal = q.witnessed.normal :=
  OpenSelectedReplay.replay_normal h

/-- Replay certificates also give native LetCase equations on the actual open witnesses. -/
theorem replay_derivable (H : Ty Empty) (L : List (Ty Empty)) {n : Nat}
    {p q : ReadTree (H :: L) n} (h : Replay (H :: L) p q) :
    Derivable false (Finite.Extensional.Selected.equation H L p q) :=
  OpenSelectedReplay.replay_derivable H L h

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay
