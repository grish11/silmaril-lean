module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Example.Bank.Defs

/-! A Boolean Φ reads a byte through two producers, independently of the old flag. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Support.Example

open SCCP.Example (word)
open SCCP.Example.Bank (fields Op model facts observe)
open Diamond (Ty)
open Diamond.SCCP (tupleFacts)
open Semantics.Dataflow (Flat)

abbrev Sigs : List (List (Ty Unit)) := [[.value word], [.value .predicate]]

/-- The flag's feedback is `isZero (advance capturedFlag oldByte)`.
The byte feeds back directly. The carried flag is no producer's operand. -/
def graph : Graph Op fields fields [] Sigs word where
  preheader := .nil
  header :=
    .cons .advance (.cons (.arg .head) (.cons (.arg (.tail (.tail (.tail .head)))) .nil))
      (.cons .isZero (.cons (.output (0 : Fin 1) .head) .nil) .nil)
  phiInputs
    | .entry => .cons (.arg .head) (.cons (.arg (.tail .head)) .nil)
    | .backedge => .cons (.output (1 : Fin 2) .head)
        (.cons (.arg (.tail (.tail (.tail .head)))) .nil)
  predicate := .arg .head
  result := .arg (.tail (.tail (.tail .head)))

def before : State model.value fields word :=
  ({incomingIndex .entry, incomingIndex .backedge}, tupleFacts (facts true 255), ⊥)

def changedFlag : State model.value fields word := Phi.write before (0 : Fin 2) .overdefined
def changedByte : State model.value fields word := Phi.write before (1 : Fin 2) .overdefined

def flagSupport : List Nat :=
  ((List.finRange 2).filter (fun i => decide (i ∈ feedbackSupport graph (0 : Fin 2)))).map Fin.val

def wakeAfterFlag : List (Split.Job 2) :=
  Split.wake model graph (facts true 255) before changedFlag []

def wakeAfterByte : List (Split.Job 2) :=
  Split.wake model graph (facts true 255) before changedByte []

def solveReport : Bool × Bool × (Flat Bool × Flat Nat) × Flat Nat :=
  let state := Split.solve model graph (facts true 255)
  (decide (incomingIndex .backedge ∈ state.1), decide (exitIndex ∈ state.1),
    observe state.2.1, state.2.2.map BitVec.toNat)

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Support.Example
