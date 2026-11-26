module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.SumBind.Continuation.Defs

/-! # The recursive operand fragment of outward call replay -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native.SumBind.Recursive

/-- Calls, injections, unary and binary lets, ordered pairs, cases,
and empty elimination can recur in every operand. Variables and unit are leaves. -/
def Admitted {Φ : Type*} : Tm Φ → Prop
  | .op _ a | .inl a | .inr a | .abort a => Admitted a
  | .let₁ a b | .let₂ a b | .pair a b => Admitted a ∧ Admitted b
  | .case e l r => Admitted e ∧ Admitted l ∧ Admitted r
  | .var _ | .unit => True

/-- Concatenate the request words of a producing schedule and its continuation.
The output label comes from the continuation. Specializing a known tag can
delete paths from this list. -/
def appendPaths {Φ : Type*} (before after : List (List Φ × Nat)) : List (List Φ × Nat) :=
  before.flatMap fun p => after.map fun q => (p.1 ++ q.1, q.2)

end Silmaril.Isotope.LambdaSSA.Acyclic.Native.SumBind.Recursive
