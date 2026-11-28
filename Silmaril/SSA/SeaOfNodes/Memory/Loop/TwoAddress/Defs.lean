module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Defs

/-! An ordered memory loop with two address Phis and one memory Phi. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress

open RVSDG (Port Tuple)

abbrev activationArgs (args : List ValueSort) := .address :: .address :: args

/-- Each entry operand reads a captured port. Each feedback operand can
read either old lane or a captured address. -/
structure Graph (args : List ValueSort) where
  activation : Loop.Graph (activationArgs args)
  entryFirst : Port args .address
  entrySecond : Port args .address
  feedbackFirst : Port (activationArgs args) .address
  feedbackSecond : Port (activationArgs args) .address

structure Header (cells : Nat) where
  first : Address cells
  second : Address cells
  heap : Heap cells

variable {args : List ValueSort} {cells : Nat}

def Header.operands (header : Header cells) (input : Tuple (Val cells) args) :
    Tuple (Val cells) (activationArgs args) :=
  .cons header.first (.cons header.second input)

def Graph.seed (graph : Graph args) (input : Tuple (Val cells) args) (heap : Heap cells) : Header cells :=
  ⟨input.get graph.entryFirst, input.get graph.entrySecond, heap⟩

/-- Resolve both Phi operands against the same old bank. The memory
operand comes from the completed activation. -/
def Graph.feedback (graph : Graph args) (input : Tuple (Val cells) args) (header : Header cells)
    (heap : Heap cells) : Header cells :=
  let previous := header.operands input
  ⟨previous.get graph.feedbackFirst, previous.get graph.feedbackSecond, heap⟩

def Graph.step (graph : Graph args) (input : Tuple (Val cells) args) (header : Header cells) :
    (Word × Heap cells) ⊕ Header cells :=
  (graph.activation.step (header.operands input) header.heap).map id (graph.feedback input header)

/-- A backedge allowance of zero still executes the initial header. -/
def Graph.evalWithin (graph : Graph args) (input : Tuple (Val cells) args) :
    Nat → Header cells → Option (Word × Heap cells)
  | 0, header => (graph.step input header).elim some (fun _ => none)
  | budget + 1, header => (graph.step input header).elim some (graph.evalWithin input budget)

def Graph.Returns (graph : Graph args) (input : Tuple (Val cells) args) (heap : Heap cells)
    (word : Word) (final : Heap cells) : Prop :=
  ∃ budget, graph.evalWithin input budget (graph.seed input heap) = some (word, final)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress
