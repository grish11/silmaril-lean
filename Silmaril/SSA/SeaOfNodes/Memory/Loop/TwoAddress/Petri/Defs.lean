module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Petri.Defs

/-! The two address values and whole heap are carried directly by one numbered θ. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Petri

open RVSDG (Origin Port Tuple Wires)
open RVSDG.OrderedRuntime.Structured (Threaded Ty runtimePort)
open SeaOfNodes.Loop (argWires)

variable {args : List ValueSort} {cells : Nat}

abbrev Packet (args : List ValueSort) := RVSDG.Theta.BodyResults (carrier (activationArgs args))

/-- Keep the tag, captured values and live heap. Both selected address
wires come from the original packet. -/
def route (graph : Graph args) {F : Ty ValueSort → Type} (packet : Tuple F (Packet args)) :
    Tuple F (Packet args) :=
  match packet with
  | .cons tag (.cons _ (.cons _ rest)) =>
    .cons tag (.cons (packet.get (.tail (argumentPort graph.feedbackFirst)))
      (.cons (packet.get (.tail (argumentPort graph.feedbackSecond))) rest))

/-- Change only the region's result wiring. The ordered body and its
tail comparison keep their original nodes and memory edges. -/
def routeReturns (graph : Graph args) :
    {past sigs : List (List (Ty ValueSort))} →
    RVSDG.Term ThetaOpcode (carrier (activationArgs args)) past sigs (Packet args) →
    RVSDG.Term ThetaOpcode (carrier (activationArgs args)) past sigs (Packet args)
  | _, _, .ret results => .ret (route graph results)
  | _, _, .bind node children rest => .bind node children (routeReturns graph rest)

def lowerBody (graph : Graph args) :
    RVSDG.Term ThetaOpcode (carrier (activationArgs args)) [] graph.activation.thetaSigs (Packet args) :=
  routeReturns graph graph.activation.thetaBody

def encodeHeader (header : Header cells) (input : Tuple (Val cells) args) :
    Tuple (WireVal cells) (carrier (activationArgs args)) :=
  encodeInput header.heap (header.operands input)

/-- The numbered activation used as the child of the emitted θ. -/
def lowerActivation (graph : Graph args) :
    RVSDG.NestedTheta.Graph ThetaOpcode (carrier (activationArgs args)) []
      graph.activation.thetaSigs (Packet args) :=
  (RVSDG.NestedTheta.Term.ofBase (lowerBody graph)).toGraph

/-- The exact activation result, including the tail tag and both routed
addresses. The stop path also produces this packet, then discards the addresses. -/
def activationPacket (graph : Graph args) (input : Tuple (Val cells) args) (header : Header cells) :
    Tuple (WireVal cells) (Packet args) :=
  match graph.step input header with
  | .inl (_, final) => .cons ⟨0⟩ (encodeHeader (graph.feedback input header final) input)
  | .inr next => .cons ⟨1⟩ (encodeHeader next input)

/-- The two entry operands are captured ports of the outer region. -/
def entryWires (graph : Graph args) : Wires (carrier args) [] (carrier (activationArgs args)) :=
  .cons (.arg (argumentPort graph.entryFirst))
    (.cons (.arg (argumentPort graph.entrySecond)) (argWires (carrier args) []))

/-- The θ owns both address lanes and the whole live heap. The outer
region returns the invariant stop word and the final heap. -/
def lowerTerm (graph : Graph args) :
    RVSDG.NestedTheta.Term ThetaOpcode (carrier args) [] [carrier (activationArgs args)] (Threaded wordPorts) :=
  let carried := carrier (activationArgs args)
  .bind ⟨carried, .theta carried, entryWires graph, fun _ => graph.activation.thetaSigs⟩
    (fun _ => .ofBase (lowerBody graph))
    (.ret (.cons (.output (0 : Fin 1) (argumentPort graph.activation.stop))
      (.cons (.output (0 : Fin 1) (runtimePort (dataPorts (activationArgs args)))) .nil)))

def lower (graph : Graph args) :
    RVSDG.NestedTheta.Graph ThetaOpcode (carrier args) [] [carrier (activationArgs args)] (Threaded wordPorts) :=
  (lowerTerm graph).toGraph

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Petri
