module

public import Silmaril.Logic.Kore.Modules.Fuel.Thms
public import Silmaril.Logic.Kore.Modules.Semantics.Modules.Examples

@[expose] public section
namespace Silmaril.Logic.Kore.Modules.Fuel.Examples
open Silmaril.Logic.Kore.Modules.Semantics.Examples (captureSource falseSource)
open Silmaril.Logic.Kore.Modules.Examples (checked model)

/-- The actual parsed alias/binder claim keeps its complete typed sentence. -/
theorem source_capture_stable (extra : Nat) :
    Checking.sentence checked.ambient (captureSource.fuel + extra) captureSource.raw =
      some captureSource.sentence :=
  Checking.sentence_add checked.ambient captureSource.fuel extra captureSource.raw
    captureSource.sentence captureSource.elaborated

/-- Increasing the accepted budget preserves the genuine false-claim control. -/
theorem source_false_stable (extra : Nat) :
    ¬ Semantics.Satisfies model (falseSource.fuel + extra) falseSource.raw := by
  intro h
  exact Semantics.Examples.actual_source_false
    ((Semantics.satisfies_add model falseSource.fuel extra falseSource.raw
      falseSource.sentence falseSource.elaborated).1 h)

/-- Exhaustion inside negation is a concrete obstacle to unconditional stability.
At budget 1 the child is empty, while budget 2 reaches top. -/
theorem failed_input_changes_meaning :
    Semantics.denote model 1 [] "S" (.not "S" (.top "S")) = Set.univ ∧
    Semantics.denote model 2 [] "S" (.not "S" (.top "S")) = ∅ := by
  have knownSort : Checking.namedSort checked.ambient "S" = true := by decide +kernel
  constructor <;> ext result <;> simp [Semantics.denote, knownSort]
end Silmaril.Logic.Kore.Modules.Fuel.Examples
