module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Comparison.CanonicalLive.Admission.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CanonicalLiveAdmission

/-! # Completeness of the admitted selected comparison -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay.CanonicalLive

open Silmaril
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open Paper.WithComputedProductProducers.Intrinsic.CaseTree.ReplyAgreement (replyContext)

/-- Exhausting the input search establishes agreement at every assignment. -/
theorem AssignmentSearch.trace_agrees_of_no_difference {L : List (Ty Empty)} {n : Nat}
    (p q : Finite.Normal L n) (h : AssignmentSearch.normalDifference? p q = none)
    (env : Finite.Assignment n) : p.traceTree env = q.traceTree env :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CanonicalLiveAdmission.trace_agrees_of_no_difference p q h env

/-- If both exact admissions are inferred, comparison returns a native
equality proof or a checked distinguishing input. -/
theorem compareSelected_ne_unknown {L : List (Ty Empty)} {n : Nat} (p q : SelectedAt (replyContext n) L)
    (hp : (admitSelected? p).isSome) (hq : (admitSelected? q).isSome) :
    compareSelected p q ≠ .unknown :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CanonicalLiveAdmission.compareSelected_ne_unknown p q hp hq

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay.CanonicalLive
