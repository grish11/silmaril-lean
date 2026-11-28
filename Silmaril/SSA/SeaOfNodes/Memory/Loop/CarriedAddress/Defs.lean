module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Defs

/-! An ordered memory loop with one address Phi and one memory Phi. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress

open RVSDG (Port Tuple)
open SeaOfNodes.Loop (Incoming)

variable {args : List ValueSort} {cells : Nat}

/-- The leading activation operand is an address Phi. Its two operand
columns name typed entry ports, so either selection is in bounds. -/
structure Graph (args : List ValueSort) where
  activation : Loop.Graph (.address :: args)
  entryAddress : Port args .address
  backedgeAddress : Port args .address

def Graph.operands (graph : Graph args) (input : Tuple (Val cells) args) (arrival : Incoming) :
    Tuple (Val cells) (.address :: args) :=
  .cons (input.get (arrival.select graph.entryAddress graph.backedgeAddress)) input

/-- Execute one activation with the address selected by the arriving
occurrence. The supplied heap is the initialized heap at entry or the
previous activation's entire post-store heap at feedback. -/
def Graph.step (graph : Graph args) (input : Tuple (Val cells) args) (arrival : Incoming)
    (heap : Heap cells) : (Word × Heap cells) ⊕ Heap cells :=
  graph.activation.step (graph.operands input arrival) heap

/-- Observe an exit within the allowed backedges. Every restart changes
the arriving occurrence to backedge and supplies the new heap. -/
def Graph.evalWithin (graph : Graph args) (input : Tuple (Val cells) args) :
    Nat → Incoming → Heap cells → Option (Word × Heap cells)
  | 0, arrival, heap => (graph.step input arrival heap).elim some (fun _ => none)
  | budget + 1, arrival, heap =>
    (graph.step input arrival heap).elim some (graph.evalWithin input budget .backedge)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress
