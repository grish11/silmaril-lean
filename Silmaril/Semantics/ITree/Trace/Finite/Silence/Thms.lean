module

public import Silmaril.Semantics.ITree.Trace.Finite.Silence.Defs
public import Silmaril.Semantics.ITree.Trace.Finite.Thms
public import Silmaril.Semantics.ITree.Trace.Silence.Thms
import Silmaril.Proofs.Semantics.ITree.Trace.Finite.Silence

@[expose] public section

namespace Silmaril.Elgot.ITree.Finite

universe u

variable {Q : Type} {R S : Type u} [DecidableEq S]

/-- In a closed finite table with no explicit stop, the silent normalizer
can report no root only after reaching a nonempty silent cycle. -/
theorem headFrom_stop_has_cycle (step : S → Step Q R S) (states : Finset S)
    (complete : ∀ state, state ∈ states) (noStop : ∀ state, step state ≠ .inl .stop) (state : S)
    (stopped : headFrom step states state = .stop) :
    ∃ last, Relation.ReflTransGen (SilentEdge step) state last ∧
      Relation.TransGen (SilentEdge step) last last :=
  Proofs.Semantics.Elgot.ITree.Finite.stop_has_cycle step states complete noStop state stopped

theorem silentAfter?_iff [DecidableEq Q] (step : S → Step Q R S) (states : Finset S) (complete : ∀ s, s ∈ states)
    (state : S) (path : ExchangePath (Event Q)) :
    silentAfter? step states state path = true ↔ SilentAfter (evaluate step state) path :=
  Proofs.Semantics.Elgot.ITree.Finite.silent_after_exact step states complete state path

end Silmaril.Elgot.ITree.Finite
