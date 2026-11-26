module

public import Silmaril.Semantics.ITree.Trace.Defs

/-! # A silent endpoint after finitely many typed exchanges -/

@[expose] public section

namespace Silmaril.Elgot.ITree

universe u v

/-- A path records only completed requests and their typed replies. -/
inductive ExchangePath (E : Type u → Type u) where
  | nil
  | cons {R : Type u} (event : E R) (reply : R) (tail : ExchangePath E)

variable {E : Type u → Type u} {A : Type v}

/-- After following the given exchanges, silent normalization has no visible
root. The endpoint distinguishes this case from a return or pending request. -/
def SilentAfter (t : Tree E A) : ExchangePath E → Prop
  | .nil => out t = Part.none
  | .cons event reply tail =>
    ∃ k, out t = Part.some (.vis event k) ∧ SilentAfter (k reply) tail

/-- Include the ordinary finite traces and the finite paths with a silent
endpoint. The endpoint is the weak tree's no-root observation. -/
def TraceLEWithSilence (t s : Tree E A) : Prop :=
  TraceLE t s ∧ ∀ path, SilentAfter t path → SilentAfter s path

end Silmaril.Elgot.ITree
