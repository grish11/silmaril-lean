module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Boundary.Defs
import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Splice.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Memory.RVSDG.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Boundary.Proofs

open RVSDG (Tuple Wires)
open RVSDG.OrderedRuntime.Structured (Data Threaded runtime runtimePort withRuntime read_cons)
open RVSDG.NestedTheta.ExplicitRuntime (EntryChecked)
open RVSDG.NestedTheta.Institution
open Memory.Diamond.Institution (PortMap pullInput)

variable {ambient next : List ValueSort} {cells : Nat}

set_option backward.isDefEq.respectTransparency false

private theorem port_wordPort (wiring : Wiring ambient next) : wiring.port wiring.wordPort = .head := by
  induction wiring with
  | word _ => rfl
  | forward _ _ ih => exact ih

theorem select_word (wiring : Wiring ambient next) (word : Word) (captures : Tuple (Val cells) ambient) :
    (wiring.select word captures).get wiring.wordPort = word := by
  rw [Wiring.select, Memory.Diamond.Institution.pullInput_get, port_wordPort]
  rfl

private theorem heap_get (heap : Heap cells) (input : Tuple (Val cells) ambient) :
    (encodeInput heap input).get (runtimePort (dataPorts ambient)) = heap := by
  induction input with
  | nil => rfl
  | cons value rest ih => exact ih

private theorem captureWires_read (ports : PortMap next ambient) (input : Tuple (Val cells) ambient)
    (heap : Heap cells) :
    Wires.read (withRuntime (.arg (runtimePort (dataPorts ambient))) (captureWires ambient next ports))
        (encodeInput heap input) PUnit.unit =
      encodeInput heap (pullInput ports input) := by
  induction next with
  | nil =>
    exact congrArg (fun heap : Heap cells => Tuple.cons (F := WireVal cells) (t := runtime) heap .nil)
      (heap_get heap input)
  | cons sort rest ih =>
    simp only [captureWires, withRuntime, read_cons, pullInput, encodeInput]
    change Tuple.cons ((encodeInput heap input).get (argumentPort (ports .head))) _ = _
    rw [encodeInput_get, ih]

private theorem adapterWires_read (wiring : Wiring ambient next) (word : Word)
    (captures : Tuple (Val cells) ambient) (postHeap : Heap cells) :
    Wires.read (withRuntime (.arg (runtimePort (dataPorts (.word :: ambient)))) (adapterWires wiring))
        (packet word captures postHeap) PUnit.unit =
      packet word (wiring.select word captures) postHeap := by
  simp only [adapterWires, withRuntime, read_cons]
  exact congrArg (Tuple.cons (F := WireVal cells) (t := .value .word) word)
    (captureWires_read wiring.port (Tuple.cons (F := Val cells) (t := ValueSort.word) word captures) postHeap)

theorem adapter_run (wiring : Wiring ambient next) (fuel : Nat) (word : Word)
    (captures : Tuple (Val cells) ambient) (postHeap : Heap cells) :
    (adapter wiring).run (thetaRuntime cells) fuel (packet word captures postHeap) =
      some (packet word (wiring.select word captures) postHeap) := by
  change some (Wires.read (withRuntime (.arg (runtimePort (dataPorts (.word :: ambient)))) (adapterWires wiring))
    (packet word captures postHeap) PUnit.unit) = _
  rw [adapterWires_read]

theorem adapter_observe (wiring : Wiring ambient next) (word : Word)
    (captures : Tuple (Val cells) ambient) (postHeap : Heap cells) :
    RuntimeObservation.observe (P := target) (thetaRuntime cells) (adapter wiring)
        (packet word captures postHeap) =
      Part.some (packet word (wiring.select word captures) postHeap) :=
  (RVSDG.NestedTheta.Partial.observe_ofRuntime_eq_some_iff_returns (thetaRuntime cells) (adapter wiring) _ _).mpr
    ⟨0, adapter_run wiring 0 word captures postHeap⟩

theorem adapter_finishes_iff (wiring : Wiring ambient next) (word : Word)
    (captures : Tuple (Val cells) ambient) (postHeap : Heap cells)
    (output : Tuple (WireVal cells) (carrier (.word :: next))) :
    RVSDG.NestedTheta.Petri.Finishes (thetaRuntime cells) (adapter wiring)
        (packet word captures postHeap) output ↔
      output = packet word (wiring.select word captures) postHeap := by
  rw [RVSDG.NestedTheta.Petri.finishes_iff]
  constructor
  · rintro ⟨fuel, observed⟩
    exact Option.some.inj (observed.symm.trans (adapter_run wiring fuel word captures postHeap))
  · rintro rfl
    exact ⟨0, adapter_run wiring 0 word captures postHeap⟩

theorem splice_observe (wiring : Wiring ambient next) {outs : List (RVSDG.OrderedRuntime.Structured.Ty ValueSort)}
    {data : Data outs} {sigs : List (List (RVSDG.OrderedRuntime.Structured.Ty ValueSort))}
    {consumer : RVSDG.NestedTheta.Graph ThetaOpcode (carrier (.word :: next)) [] sigs (Threaded outs)}
    (consumerChecked : EntryChecked (a := inputData (.word :: next)) (b := data) consumer.toTerm)
    (word : Word) (captures : Tuple (Val cells) ambient) (postHeap : Heap cells) :
    RuntimeObservation.observe (P := target) (thetaRuntime cells) (splice wiring consumerChecked)
        (packet word captures postHeap) =
      RuntimeObservation.observe (P := target) (thetaRuntime cells) consumer
        (packet word (wiring.select word captures) postHeap) := by
  unfold splice RuntimeObservation.observe
  rw [RVSDG.NestedTheta.ExplicitRuntime.Splice.graph_observe]
  change (RuntimeObservation.observe (P := target) (thetaRuntime cells) (adapter wiring)
    (packet word captures postHeap)).bind _ = _
  rw [adapter_observe, Part.bind_some]

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
        (packet word (wiring.select word captures) postHeap) output := by
  simp only [RVSDG.NestedTheta.Petri.finishes_iff,
    ← RVSDG.NestedTheta.Partial.observe_ofRuntime_eq_some_iff_returns]
  exact iff_of_eq (congrArg (· = Part.some output) (splice_observe wiring consumerChecked word captures postHeap))

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Boundary.Proofs
