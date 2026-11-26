module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Example.Bank.Defs

/-! Execute destination jobs on the existing mixed Boolean/byte bank. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Example

open SCCP.Example (word)
open SCCP.Example.Bank (fields model graph facts observe)
open Diamond.SCCP (tupleFacts)
open Semantics.Dataflow (Flat)

def beforeWidening : State model.value fields word :=
  ({incomingIndex .entry, incomingIndex .backedge}, tupleFacts (facts true 0), ⊥)

/-- The word visit widens the word and wakes its own equation. The direct
flag feedback reads only the unchanged flag, so its job is absent. -/
def widening (pending : List (Job fields)) : (Flat Bool × Flat Nat) × List Nat :=
  let next := step model (graph false) (facts true 0) (1 : Fin 2) beforeWidening pending
  (observe next.1.2.1, next.2.map Fin.val)

def crossSnapshot : State model.value fields word :=
  ({incomingIndex .backedge}, tupleFacts (facts false 0), ⊥)

/-- Compare writing two facts prepared from one snapshot with re-evaluating
the second equation after publishing the first. -/
def feedbackReads : (Flat Bool × Flat Nat) × (Flat Bool × Flat Nat) :=
  let source := graph true
  let input := facts false 0
  let wordJob : Fin 2 := 1
  let afterFlag := update model source input (0 : Fin 2) crossSnapshot
  let frozenWord := evaluate model source input wordJob (dependencies model source input crossSnapshot wordJob)
  (observe (write afterFlag wordJob frozenWord).2.1,
    observe (update model source input wordJob afterFlag).2.1)

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Example
