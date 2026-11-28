module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Example.Bank.Defs

/-! A Boolean and byte notify two overlapping, cross-field Φ destinations. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index.Example

open SCCP.Example (word)
open SCCP.Example.Bank (fields model graph facts observe)
open Diamond.SCCP (tupleFacts)
open Semantics.Dataflow (Flat)

def index := Index.build (graph true)

/-- The old flag feeds the byte Φ. The old byte feeds both Φ jobs. -/
def readerReport : List (List Nat) :=
  (List.finRange 2).map fun field => index.readers[field.val].sort.map Fin.val

def before : State model.value fields word :=
  ({incomingIndex .entry, incomingIndex .backedge, exitIndex}, tupleFacts (facts false 0), ⊥)

def widenedFlag : State model.value fields word :=
  Phi.write before (0 : Fin 2) .overdefined

def widened : State model.value fields word :=
  Phi.write widenedFlag (1 : Fin 2) .overdefined

def flagOnly : List (Job 2) :=
  Index.wake model index before widenedFlag []

def multiTrigger : List (Job 2) :=
  Index.wake model index before widened []

def prequeued : List (Job 2) :=
  Index.wake model index before widened [.phi (1 : Fin 2)]

def withoutFeedback (state : State model.value fields word) : State model.value fields word :=
  (state.1.erase (incomingIndex .backedge), state.2)

def gated : List (Job 2) :=
  Index.wake model index (withoutFeedback before) (withoutFeedback widened) []

def activation : List (Job 2) :=
  Index.wake model index (withoutFeedback before) before []

def activationAndFields : List (Job 2) :=
  Index.wake model index (withoutFeedback before) widened [.result, .phi (0 : Fin 2)]

def solveReport : Bool × Bool × (Flat Bool × Flat Nat) × Flat Nat :=
  let state := Index.solve model (facts false 0) index
  (decide (incomingIndex .backedge ∈ state.1), decide (exitIndex ∈ state.1),
    observe state.2.1, state.2.2.map BitVec.toNat)

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index.Example
