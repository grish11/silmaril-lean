module

public import Silmaril.Semantics.ITree.Trace.Finite.Defs
public import Silmaril.Semantics.ITree.Trace.Thms
import Silmaril.Proofs.Semantics.ITree.Trace.Finite.Compare
import Silmaril.Proofs.Semantics.ITree.Trace.Finite.Observe

@[expose] public section

namespace Silmaril.Elgot.ITree.Finite

universe u v
variable {Q : Type} {Reply : Q → Type} {R S T : Type u} [DecidableEq S]

/-- A full-state revisit during silent normalization has no visible root. -/
theorem out_evaluate (step : S → Step Q R S Reply) (states : Finset S)
    (complete : ∀ s, s ∈ states) (s : S) :
    out (evaluate step s) = (headFrom step states s).render (evaluate step) :=
  Proofs.Semantics.Elgot.ITree.Finite.out_evaluate step states complete s

/-- Product-state simulation decides the finite weak trace order, including
pending requests, all typed replies, and terminating results. -/
theorem compare_iff [DecidableEq T] [DecidableEq Q] [DecidableEq R] [∀ key, Fintype (Reply key)]
    (statesL : Finset S) (statesR : Finset T) (completeL : ∀ s, s ∈ statesL)
    (completeR : ∀ t, t ∈ statesR) (left : S → Step Q R S Reply) (right : T → Step Q R T Reply)
    (s : S) (t : T) :
    compare statesL statesR left right s t = true ↔ TraceLE (evaluate left s) (evaluate right t) :=
  Proofs.Semantics.Elgot.ITree.Finite.compare_exact statesL statesR completeL completeR left right s t

/-- Compare finite traces along replies admitted by the shared stateless
handler. The target sees the same admitted path whenever it has the trace. -/
theorem compareUnder_iff [DecidableEq T] [DecidableEq Q] [DecidableEq R] [∀ key, Fintype (Reply key)]
    (admits : ∀ key, Reply key → Bool)
    (statesL : Finset S) (statesR : Finset T) (completeL : ∀ s, s ∈ statesL)
    (completeR : ∀ t, t ∈ statesR) (left : S → Step Q R S Reply) (right : T → Step Q R T Reply)
    (s : S) (t : T) :
    compareUnder admits statesL statesR left right s t = true ↔
      ∀ trace, HandledTrace (replyHandler admits) () (evaluate left s) trace → HasTrace (evaluate right t) trace :=
  Proofs.Semantics.Elgot.ITree.Finite.compareUnder_exact admits statesL statesR completeL completeR left right s t

/-- The finite product decides inclusion of actual handled traces at one
initial handler state. The target can reuse the source replay. -/
theorem compareWithHandler_iff [DecidableEq T] [DecidableEq Q] [DecidableEq R] [∀ key, Fintype (Reply key)]
    {H : Type v} [DecidableEq H] (advance : H → ∀ key, Reply key → Option H)
    (statesL : Finset S) (statesR : Finset T) (statesH : Finset H)
    (completeL : ∀ s, s ∈ statesL) (completeR : ∀ t, t ∈ statesR) (completeH : ∀ h, h ∈ statesH)
    (left : S → Step Q R S Reply) (right : T → Step Q R T Reply) (s : S) (t : T) (h : H) :
    compareWithHandler advance statesL statesR statesH left right s t h = true ↔
      ∀ trace, HandledTrace (statefulReplyHandler advance) h (evaluate left s) trace →
        HasTrace (evaluate right t) trace :=
  Proofs.Semantics.Elgot.ITree.Finite.compareWithHandler_exact advance statesL statesR statesH
    completeL completeR completeH left right s t h

end Silmaril.Elgot.ITree.Finite
