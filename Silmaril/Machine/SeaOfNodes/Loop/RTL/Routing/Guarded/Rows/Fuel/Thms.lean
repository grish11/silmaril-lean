module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Thms
public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Fuel.Thms
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Correctness

/-! # Exact finite returns and matched budgets for the emitted guarded row -/

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (model word)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (inputEnv instruction)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

variable {arity : Nat}

/-- Exact RTL fuel threshold from the number of completed native backedges. -/
theorem runMain_fuel_iff (p : Plan arity) (input : WordTuple arity) (initial final : Memory)
    (returned : List Word) (fuel : Nat) :
    (lowerBank p.graph).runMain fuel 0 (words input) initial = .returned returned final ↔
      ∃ count value, p.graph.ReturnsAfter model input count (p.graph.initial model input) value ∧
        p.rtlFuel count ≤ fuel ∧ returned = [value] ∧ final = initial :=
  Proofs.runMain_fuel_iff p input initial final returned fuel

/-- Whole machine returns preserve the native returned word and all memory. -/
theorem rtl_returns_iff (p : Plan arity) (input : WordTuple arity) (initial final : Memory) (returned : List Word) :
    (lowerBank p.graph).oracle 0 (words input) initial returned final ↔
      ∃ value : Word, p.graph.Returns model input value ∧ returned = [value] ∧ final = initial :=
  Proofs.rtl_returns_iff p input initial final returned

/-- Compare the actual runners with fuel for the same maximum number of
backedges, including the exit visit. -/
theorem bounded_returns_iff (p : Plan arity) (input : WordTuple arity) (initial final : Memory)
    (returned : List Word) (budget : Nat) :
    (lowerBank p.graph).runMain (p.rtlFuel budget) 0 (words input) initial = .returned returned final ↔
      ∃ value : Word, Generic.Fuel.run model (inputEnv model input) (budget + 1) (Generic.lower p.graph) =
        some (0, Generic.packResult model (out := word) value) ∧
        returned = [value] ∧ final = initial :=
  Proofs.bounded_returns_iff p input initial final returned budget

/-- At those same budgets both runners agree on absence of a return. -/
theorem bounded_absence_iff (p : Plan arity) (input : WordTuple arity) (initial : Memory) (budget : Nat) :
    ((lowerBank p.graph).runMain (p.rtlFuel budget) 0 (words input) initial).returnedValues? = none ↔
      Generic.Fuel.run model (inputEnv model input) (budget + 1) (Generic.lower p.graph) = none :=
  Proofs.bounded_absence_iff p input initial budget

/-- Finite returns of the checked targets agree in both directions with
exact whole-memory equality. -/
theorem returns_iff {spec : Spec} {targets : Checked.Phi.Targets}
    (accepted : lowerChecked arity spec = some targets) (input : WordTuple arity)
    (initial final : Memory) (returned : List Word) :
    targets.1.oracle 0 (words input) initial returned final ↔
      ∃ value : Word, returned = [value] ∧
        Eval (instruction model) (inputEnv model input) targets.2
          initial 0 (Generic.packResult model (out := word) value) final :=
  Proofs.returns_iff accepted input initial final returned

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
