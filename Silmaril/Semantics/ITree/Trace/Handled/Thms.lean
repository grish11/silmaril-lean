module

public import Silmaril.Semantics.ITree.Trace.Handled.Defs
public import Silmaril.Semantics.ITree.Trace.Thms
import Silmaril.Proofs.Semantics.ITree.HandledTrace

public section

namespace Silmaril.Elgot.ITree

universe u v w

variable {E : Type u → Type u} {X : Type w} {A B C : Type v}
  {step : Handler X E} {x : X}

@[refl] theorem HandledTraceLE.refl (t : Tree E A) : HandledTraceLE step x t t :=
  fun _ seen => seen

theorem HandledTraceLE.trans {t s r : Tree E A}
    (left : HandledTraceLE step x t s) (right : HandledTraceLE step x s r) :
    HandledTraceLE step x t r :=
  fun p seen => right p (left p seen)

/-- Each reachable return is retained with its full payload and the same
possible replay state. -/
theorem HandledTraceLE.returnsTo {t s : Tree E A} {y : X} {a : A}
    (h : HandledTraceLE step x t s) (reached : ReturnsTo step x t y a) :
    ReturnsTo step x s y a :=
  Silmaril.Proofs.Semantics.Elgot.ITree.handled_returnsTo h reached

/-- Sequence both trees. The continuation comparison is needed only for
returns reachable in the source, at every handler state that their exact
exchange path can reach. -/
theorem HandledTraceLE.bind {t s : Tree E A} {f g : A → Tree E B}
    (producer : HandledTraceLE step x t s)
    (continuation : ∀ {y a}, ReturnsTo step x t y a → HandledTraceLE step y (f a) (g a)) :
    HandledTraceLE step x (t >>= f) (s >>= g) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.handled_bind producer continuation

/-- A common continuation preserves inclusion when it receives the entire
compared return, with the same typed path replayed from the same state. -/
theorem HandledTraceLE.bind_left {t s : Tree E A} (h : HandledTraceLE step x t s)
    (f : A → Tree E B) : HandledTraceLE step x (t >>= f) (s >>= f) :=
  h.bind (fun _ => .refl _)

/-- A projected comparison suffices for contexts that receive the return
through that projection. For a store-reading context the compared return
must carry the part of the final store the context reads. -/
theorem HandledTraceLE.bind_projected {t s : Tree E A} (project : A → B)
    (h : HandledTraceLE step x (t >>= fun a => pure (project a)) (s >>= fun a => pure (project a)))
    (f : B → Tree E C) : HandledTraceLE step x (t >>= fun a => f (project a))
      (s >>= fun a => f (project a)) := by
  simpa only [bind_assoc, pure_bind] using h.bind_left f

end Silmaril.Elgot.ITree
