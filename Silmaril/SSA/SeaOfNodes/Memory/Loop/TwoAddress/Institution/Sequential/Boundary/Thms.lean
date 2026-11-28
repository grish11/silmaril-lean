module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Boundary.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Boundary.Correctness
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Boundary.Reindex

/-! Packet equality and observation of the existing numbered splice. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Boundary

open RVSDG (Tuple)
open RVSDG.OrderedRuntime.Structured (Data Threaded)
open RVSDG.NestedTheta.ExplicitRuntime (EntryChecked)
open RVSDG.NestedTheta.Institution
open Memory.Diamond.Institution (PortMap pullInput)

variable {ambient next : List ValueSort} {cells : Nat}

theorem Wiring.select_word (wiring : Wiring ambient next) (word : Word)
    (captures : Tuple (Val cells) ambient) : (wiring.select word captures).get wiring.wordPort = word :=
  Proofs.select_word wiring word captures

theorem Wiring.map_id (wiring : Wiring ambient next) : wiring.map (fun p => p) = wiring :=
  Proofs.map_id wiring

theorem Wiring.map_comp {target after : List ValueSort} (wiring : Wiring ambient next)
    (f : PortMap ambient target) (g : PortMap target after) :
    wiring.map (fun p => g (f p)) = (wiring.map f).map g :=
  Proofs.map_comp wiring f g

theorem Wiring.select_map {target : List ValueSort} (wiring : Wiring ambient next)
    (rename : PortMap ambient target) (word : Word) (input : Tuple (Val cells) target) :
    (wiring.map rename).select word input = wiring.select word (pullInput rename input) :=
  Proofs.select_map wiring rename word input

/-- The numbered adapter forwards the entire post-heap at any fuel. -/
theorem adapter_run (wiring : Wiring ambient next) (fuel : Nat) (word : Word)
    (captures : Tuple (Val cells) ambient) (postHeap : Heap cells) :
    (adapter wiring).run (thetaRuntime cells) fuel (packet word captures postHeap) =
      some (packet word (wiring.select word captures) postHeap) :=
  Proofs.adapter_run wiring fuel word captures postHeap

theorem adapter_observe (wiring : Wiring ambient next) (word : Word)
    (captures : Tuple (Val cells) ambient) (postHeap : Heap cells) :
    RuntimeObservation.observe (P := target) (thetaRuntime cells) (adapter wiring)
        (packet word captures postHeap) =
      Part.some (packet word (wiring.select word captures) postHeap) :=
  Proofs.adapter_observe wiring word captures postHeap

/-- The actual adapter completion delivers exactly the routed packet. -/
theorem adapter_finishes_iff (wiring : Wiring ambient next) (word : Word)
    (captures : Tuple (Val cells) ambient) (postHeap : Heap cells)
    (output : Tuple (WireVal cells) (carrier (.word :: next))) :
    RVSDG.NestedTheta.Petri.Finishes (thetaRuntime cells) (adapter wiring)
        (packet word captures postHeap) output ↔
      output = packet word (wiring.select word captures) postHeap :=
  Proofs.adapter_finishes_iff wiring word captures postHeap output

/-- The numbered splice observes the checked consumer at the exact routed packet, including absence. -/
theorem splice_observe (wiring : Wiring ambient next) {outs : List (RVSDG.OrderedRuntime.Structured.Ty ValueSort)}
    {data : Data outs} {sigs : List (List (RVSDG.OrderedRuntime.Structured.Ty ValueSort))}
    {consumer : RVSDG.NestedTheta.Graph ThetaOpcode (carrier (.word :: next)) [] sigs (Threaded outs)}
    (consumerChecked : EntryChecked (a := inputData (.word :: next)) (b := data) consumer.toTerm)
    (word : Word) (captures : Tuple (Val cells) ambient) (postHeap : Heap cells) :
    RuntimeObservation.observe (P := target) (thetaRuntime cells) (splice wiring consumerChecked)
        (packet word captures postHeap) =
      RuntimeObservation.observe (P := target) (thetaRuntime cells) consumer
        (packet word (wiring.select word captures) postHeap) :=
  Proofs.splice_observe wiring consumerChecked word captures postHeap

theorem splice_finishes_iff (wiring : Wiring ambient next)
    {outs : List (RVSDG.OrderedRuntime.Structured.Ty ValueSort)}
    {data : Data outs} {sigs : List (List (RVSDG.OrderedRuntime.Structured.Ty ValueSort))}
    {consumer : RVSDG.NestedTheta.Graph ThetaOpcode (carrier (.word :: next)) [] sigs (Threaded outs)}
    (consumerChecked : EntryChecked (a := inputData (.word :: next)) (b := data) consumer.toTerm)
    (word : Word) (captures : Tuple (Val cells) ambient) (postHeap : Heap cells)
    (output : Tuple (WireVal cells) (Threaded outs)) :
    RVSDG.NestedTheta.Petri.Finishes (thetaRuntime cells) (splice wiring consumerChecked)
        (packet word captures postHeap) output ↔
      RVSDG.NestedTheta.Petri.Finishes (thetaRuntime cells) consumer
        (packet word (wiring.select word captures) postHeap) output :=
  Proofs.splice_finishes_iff wiring consumerChecked word captures postHeap output

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Boundary
