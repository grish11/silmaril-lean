module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.SumBind.Recursive.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Syntactic.Defs

/-! # Opt-in native replay for checked captured graphs -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture

open Region.Paper

universe u v w

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)] {ε : Type w} [HasEff Φ ε]

/-- Combine the existing once-bound CFG η and recursive operand replay
generators in their common typed contextual closure. -/
abbrev ReplaySeed (pe : ε) (Γ : VCtx (Ty α)) (r s : Region Φ) (L : LCtx (Ty α)) :=
  WithBoundEntryEta.Step Γ r s L ∨ Native.SumBind.Continuation.Seed pe Γ r s L

abbrev ReplayEqv (pe : ε) := Extension.Eqv (ReplaySeed (α := α) (Φ := Φ) pe)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture
