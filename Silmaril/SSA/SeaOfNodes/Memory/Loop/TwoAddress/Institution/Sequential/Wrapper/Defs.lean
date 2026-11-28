module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Boundary.Defs

/-! Preserve scalars at the outer boundary of the actual numbered θ. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Wrapper

open RVSDG (Origin Tuple Wires)
open RVSDG.NestedTheta.ExplicitRuntime (thetaNode)
open RVSDG.OrderedRuntime.Structured (nextRuntime runtimePort withRuntime)
open Memory.Diamond.Institution (PortMap)

variable {args entry outs : List ValueSort} {cells : Nat}

def producerOutput (input : Tuple (Val cells) args) :
    Tuple (WireVal cells) (carrier [.word]) → Tuple (WireVal cells) (carrier (.word :: args))
  | .cons word (.cons final .nil) => Boundary.packet word input final

def pairPacket (first second : Word) (heap : Heap cells) :
    Tuple (WireVal cells) (carrier [.word, .word]) :=
  Boundary.packet first (Tuple.cons (F := Val cells) (t := ValueSort.word) second .nil) heap

def consumerOutput (first : Word) :
    Tuple (WireVal cells) (carrier [.word]) → Tuple (WireVal cells) (carrier [.word, .word])
  | .cons word (.cons final .nil) => pairPacket first word final

/-- Choose the two initial lanes and the remaining captures out of the
outer value bank. The root θ supplies the sole heap input separately. -/
def seedWires (graph : Graph args) (ports : PortMap args entry) :
    Wires (carrier entry) [] (dataPorts (activationArgs args)) :=
  .cons (.arg (argumentPort (ports graph.entryFirst)))
    (.cons (.arg (argumentPort (ports graph.entrySecond))) (Boundary.captureWires entry args ports))

def exitWord (graph : Graph args) : Origin (carrier entry) [carrier (activationArgs args)] (.value .word) :=
  .output (0 : Fin 1) (argumentPort graph.activation.stop)

/-- Preserve the same emitted activation child and its θ. Only outer
entry and result wires are supplied by the wrapper. -/
def wrapTerm (graph : Graph args) (ports : PortMap args entry)
    (returnWires : Wires (carrier entry) [carrier (activationArgs args)] (dataPorts outs)) :
    RVSDG.NestedTheta.Term ThetaOpcode (carrier entry) [] [carrier (activationArgs args)] (carrier outs) :=
  .bind (thetaNode (.arg (runtimePort (dataPorts entry))) (seedWires graph ports) graph.activation.thetaSigs)
    (fun _ => .ofBase (Petri.lowerBody graph))
    (.ret (withRuntime (nextRuntime [] (dataPorts (activationArgs args))) returnWires))

def forwardingWires (graph : Graph args) :
    Wires (carrier entry) [carrier (activationArgs args)] (dataPorts (.word :: entry)) :=
  .cons (exitWord graph) ((Boundary.captureWires entry entry (fun p => p)).map
    (fun _ => RVSDG.NestedTheta.ExplicitRuntime.Splice.weaken (carrier (activationArgs args))))

/-- Lower a θ whose captures are selected from a larger entry bank. Keep
the entire entry bank alongside the returned word and live heap. -/
def forwarding (graph : Graph args) (ports : PortMap args entry) :
    RVSDG.NestedTheta.Graph ThetaOpcode (carrier entry) [] [carrier (activationArgs args)]
      (carrier (.word :: entry)) :=
  (wrapTerm graph ports (forwardingWires graph)).toGraph

def producerWires (graph : Graph args) :
    Wires (carrier args) [carrier (activationArgs args)] (dataPorts (.word :: args)) :=
  forwardingWires graph

/-- Forward the original ambient captures and return the actual θ result and live heap. -/
def producer (graph : Graph args) :
    RVSDG.NestedTheta.Graph ThetaOpcode (carrier args) [] [carrier (activationArgs args)] (carrier (.word :: args)) :=
  forwarding graph (fun p => p)

def consumerWires (graph : Graph args) :
    Wires (carrier (.word :: args)) [carrier (activationArgs args)] (dataPorts [.word, .word]) :=
  .cons (.arg .head) (.cons (exitWord graph) .nil)

/-- Keep the reserved word outside θ and return it with the next word and live heap. -/
def consumer (graph : Graph args) :
    RVSDG.NestedTheta.Graph ThetaOpcode (carrier (.word :: args)) [] [carrier (activationArgs args)]
      (carrier [.word, .word]) :=
  (wrapTerm graph (fun p => .tail p) (consumerWires graph)).toGraph

def thirdWires (graph : Graph args) :
    Wires (carrier (.word :: .word :: args)) [carrier (activationArgs args)] (dataPorts [.word, .word, .word]) :=
  .cons (.arg (.tail .head)) (.cons (.arg .head) (.cons (exitWord graph) .nil))

def thirdOutput (first second : Word) :
    Tuple (WireVal cells) (carrier [.word]) → Tuple (WireVal cells) (carrier [.word, .word, .word])
  | .cons third rest => .cons first (.cons second (.cons third rest))

/-- The entry bank places the most recent result first for Boundary routing.
The final return lists all three words in execution order. -/
def third (graph : Graph args) :
    RVSDG.NestedTheta.Graph ThetaOpcode (carrier (.word :: .word :: args)) [] [carrier (activationArgs args)]
      (carrier [.word, .word, .word]) :=
  (wrapTerm graph (fun p => .tail (.tail p)) (thirdWires graph)).toGraph

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Wrapper
