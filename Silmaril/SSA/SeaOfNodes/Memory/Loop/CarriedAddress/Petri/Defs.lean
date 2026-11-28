module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Petri.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Defs

/-! A numbered θ whose live child selects the address by its arrival colour. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Petri

open RVSDG (Port Tuple)
open RVSDG.NestedTheta (Term thetaVertex)
open RVSDG.OrderedRuntime.Structured (Threaded runtimePort)
open SeaOfNodes.Loop (Incoming argWires)
open Memory.Diamond.Institution (mapBody)

variable {args : List ValueSort} {cells : Nat}

/-- Interpret the leading activation argument as the chosen typed address port. -/
def addressPort (graph : Graph args) (arrival : Incoming) :
    {sort : ValueSort} → Port (.address :: args) sort → Port args sort
  | _, .head => arrival.select graph.entryAddress graph.backedgeAddress
  | _, .tail p => p

/-- The stop comparison already refers to an invariant word port. -/
def stopPort (graph : Graph args) : Port args .word :=
  match graph.activation.stop with
  | .tail p => p

theorem accesses_mapBody
    (rename : Memory.Diamond.Institution.PortMap (.address :: args) args)
    {past : List (List ValueSort)} {version : Nat} (body : Memory.Body (.address :: args) past version) :
    accesses (mapBody rename body) = accesses body := by
  induction body <;> simp_all [mapBody, accesses]

/-- Both arms reuse the ordered activation lowering with only the leading
address input rewired. All Load/Store nodes and memory edges are retained. -/
def arm (graph : Graph args) (arrival : Incoming) : Loop.Graph args where
  body := mapBody (addressPort graph arrival) graph.activation.body
  effects := (accesses_mapBody (addressPort graph arrival) graph.activation.body).trans graph.activation.effects
  stop := stopPort graph

abbrev carried (args : List ValueSort) := RVSDG.Theta.BodyResults (carrier args)

def occurrence (tag : Fin 2) : Incoming :=
  Fin.cases .entry (fun _ => .backedge) tag

def arrivalColour (arrival : Incoming) : ULift (Fin 2) :=
  ⟨arrival.select 0 1⟩

/-- Root input supplies the entry occurrence once. On a restart the waiting
θ token instead gets its new occurrence and heap from the completed child. -/
def encodeArrival (arrival : Incoming) (heap : Heap cells) (input : Tuple (Val cells) args) :
    Tuple (WireVal cells) (carried args) :=
  .cons (arrivalColour arrival) (encodeInput heap input)

abbrev bodySigs (args : List ValueSort) : List (List (RVSDG.PortType ValueSort PUnit)) :=
  [carried args]

/-- γ selects the incoming occurrence. Its result tag controls θ and is
also wired as the new occurrence. A restart therefore supplies tag one
and passes the post-effect heap, with every invariant argument unchanged. -/
def lowerBody (graph : Graph args) :
    Term ThetaOpcode (carried args) [] (bodySigs args) (RVSDG.Theta.BodyResults (carried args)) :=
  .bind ⟨_, .base (.gamma 0), argWires (carried args) [],
      fun i => (arm graph (occurrence i)).thetaSigs⟩
    (fun i => .ofBase (arm graph (occurrence i)).thetaBody)
    (.ret (.cons (.output (0 : Fin 1) .head) (RVSDG.NestedTheta.thetaResults (carried args))))

/-- The existing nested firing semantics runs this single θ from one root
marking. A stop returns the invariant stop word and the entire live heap. -/
def lowerTerm (graph : Graph args) :
    Term ThetaOpcode (carried args) [] [carried args] (Threaded wordPorts) :=
  .bind (thetaVertex (bodySigs args)) (fun _ => lowerBody graph)
    (.ret (.cons (.output (0 : Fin 1) (.tail (argumentPort (stopPort graph))))
      (.cons (.output (0 : Fin 1) (.tail (runtimePort (dataPorts args)))) .nil)))

def lower (graph : Graph args) :
    RVSDG.NestedTheta.Graph ThetaOpcode (carried args) [] [carried args] (Threaded wordPorts) :=
  (lowerTerm graph).toGraph

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Petri
