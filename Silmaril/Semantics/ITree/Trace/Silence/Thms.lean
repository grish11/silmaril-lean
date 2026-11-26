module

public import Silmaril.Semantics.ITree.Trace.Silence.Defs
public import Silmaril.Semantics.ITree.Trace.Thms
import Silmaril.Proofs.Semantics.ITree.Trace.Silence

@[expose] public section

namespace Silmaril.Elgot.ITree

universe u v

variable {E : Type u → Type u} {A B : Type v}

/-- At a visible root, compare the typed request before following a reply. -/
theorem silentAfter_vis_iff {R S : Type u} (e : E R) (k : R → Tree E A)
    (event : E S) (reply : S) (tail : ExchangePath E) :
    SilentAfter (vis e k) (.cons event reply tail) ↔
      ∃ h : S = R, h ▸ event = e ∧ SilentAfter (k (h ▸ reply)) tail :=
  Proofs.Semantics.Elgot.ITree.silent_vis_iff e k event reply tail

/-- In the deterministic weak-tree model, including silent endpoints
forces ordinary finite trace inclusion in the other direction as well. -/
theorem traceLEWithSilence_iff_mutual {t s : Tree E A} :
    TraceLEWithSilence t s ↔ TraceLE t s ∧ TraceLE s t :=
  Proofs.Semantics.Elgot.ITree.trace_with_silence_mutual

theorem silentAfter_bind_pure_iff (f : A → B) (t : Tree E A) (path : ExchangePath E) :
    SilentAfter (t >>= fun a => pure (f a)) path ↔ SilentAfter t path :=
  Proofs.Semantics.Elgot.ITree.silent_bind_pure f t path

theorem TraceLEWithSilence.bind_pure_iff {f : A → B} (hf : Function.Injective f) {t s : Tree E A} :
    TraceLEWithSilence (t >>= fun a => pure (f a)) (s >>= fun a => pure (f a)) ↔ TraceLEWithSilence t s := by
  simp only [traceLEWithSilence_iff_mutual, TraceLE.bind_pure_iff hf]

end Silmaril.Elgot.ITree
