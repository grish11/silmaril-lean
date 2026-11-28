module

public import Silmaril.Semantics.ConcurrentTrace.Thms
public import Silmaril.Semantics.ConcurrentTrace.Ideals.Thms
public import Silmaril.Semantics.ThreadTrace.Thms

/-! # Threaded computations over finite event/sync words -/

@[expose] public section

namespace Silmaril.Semantics.ConcurrentTrace.EventSync

universe u v

variable {T : Type u} {E : Type v}

/-- The finite trace quotient as a writer-output map. -/
def quotientOutput : FreeMonoid (Letter T E) →* Trace T E := (congruence T E).mk'

/-- Each event and each synchronization contributes one to the trace length. -/
def lengthHom : Trace T E →* Multiplicative Nat :=
  lift (fun _ => Multiplicative.ofAdd 1) (fun _ _ _ => rfl)

/-- Threaded nondeterminism over the finite trace monoid. -/
abbrev Nondet (T E : Type u) := ThreadTrace.Nondet T (Trace T E)

/-- Threaded nondeterminism with a branch-local used-name set. -/
abbrev Alloc (T E : Type u) := ThreadTrace.Alloc T (Trace T E)

/-- Raw allocative computations containing every representative of their output classes. -/
abbrev Complete (T E : Type u) := ThreadTrace.Complete T (quotientOutput (T := T) (E := E))

end Silmaril.Semantics.ConcurrentTrace.EventSync
