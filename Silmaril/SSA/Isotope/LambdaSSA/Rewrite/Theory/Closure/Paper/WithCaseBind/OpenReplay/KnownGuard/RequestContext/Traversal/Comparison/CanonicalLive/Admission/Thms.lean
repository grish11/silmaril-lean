module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Comparison.CanonicalLive.Admission.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CanonicalLiveAdmission

/-! # Completeness of the admitted selected comparison -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay.CanonicalLive

open Silmaril
open Paper.WithComputedProductProducers.Intrinsic.CaseTree.ReplyAgreement (replyContext)

/-- If both exact admissions are inferred, comparison returns a native
equality proof or a checked distinguishing input. -/
theorem compareSelected_ne_unknown {L : List (Ty Empty)} {n : Nat} (p q : SelectedAt (replyContext n) L)
    (hp : (admitSelected? p).isSome) (hq : (admitSelected? q).isSome) :
    compareSelected p q ≠ .unknown :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CanonicalLiveAdmission.compareSelected_ne_unknown p q hp hq

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay.CanonicalLive
