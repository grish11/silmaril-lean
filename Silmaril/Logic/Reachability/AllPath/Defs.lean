module

public import Silmaril.Logic.Reachability.Thms

/-! Guarded circularity for all-path partial reachability over arbitrary actual
transition relations. Progress includes existence of a successor: universal
successor closure alone would incorrectly admit a terminal non-target state. -/

@[expose] public section
namespace Silmaril.Logic.Reachability

variable {W : Type}

/-- A local all-path invariant allows immediate success, or actual progress with
all successors still in the invariant. Infinite executions need not hit Q. -/
structure AllPathInvariant (R : W → W → Prop) (Q I : W → Prop) : Prop where
  progress : ∀ w, I w → Q w ∨ ((∃ v, R w v) ∧ ∀ v, R w v → I v)

end Silmaril.Logic.Reachability
