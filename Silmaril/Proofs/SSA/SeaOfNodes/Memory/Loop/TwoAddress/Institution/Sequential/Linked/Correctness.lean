module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Defs
import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Splice.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Boundary.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Proofs

open RVSDG (Tuple)
open RVSDG.NestedTheta.Institution
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open CarriedAddress.Institution.Backend (runtimeResult)

variable {P Q : EntrySignature}

set_option backward.isDefEq.respectTransparency false

theorem observe_eq_numbered (first : Graph P.args) (second : Graph Q.args)
    (wiring : Boundary.Wiring P.args Q.args) (model : EntryModel P) (initial : Heap model.cells) :
    RuntimeObservation.observe (P := target) (thetaRuntime model.cells) (lower first second wiring)
        (encodeInput initial model.input) =
      (numbered (RuntimeRoom.GeneratedProgram.lower first) (RuntimeRoom.GeneratedProgram.lower second)
        model (fun word => wiring.select word model.input) initial).map (resultCodec model.cells) := by
  unfold lower RuntimeObservation.observe
  rw [RVSDG.NestedTheta.ExplicitRuntime.Splice.graph_observe]
  change (RuntimeObservation.observe (P := target) (thetaRuntime model.cells) (Wrapper.producer first)
    (encodeInput initial model.input)).bind
      (RuntimeObservation.observe (P := target) (thetaRuntime model.cells) (Boundary.splice wiring
        (Wrapper.consumerChecked second))) = _
  rw [Wrapper.producer_observe, Part.bind_map]
  simp only [numbered, Sequential.observe, numberedStage, Part.bind_map, Part.map_bind, Part.map_map]
  congr 1
  funext out
  cases out with
  | cons word rest =>
    cases rest with
    | cons mid tail =>
      cases tail
      rw [Wrapper.producerOutput, Boundary.splice_observe, Wrapper.consumer_observe]
      rfl

theorem returns_iff_numbered (first : Graph P.args) (second : Graph Q.args)
    (wiring : Boundary.Wiring P.args Q.args) (model : EntryModel P) (initial : Heap model.cells)
    (out : Result model.cells) :
    (lower first second wiring).Returns (thetaRuntime model.cells)
        (encodeInput initial model.input) (resultCodec model.cells out) ↔
      numbered (RuntimeRoom.GeneratedProgram.lower first) (RuntimeRoom.GeneratedProgram.lower second)
        model (fun word => wiring.select word model.input) initial = Part.some out := by
  rw [← RVSDG.NestedTheta.Partial.observe_ofRuntime_eq_some_iff_returns]
  change RuntimeObservation.observe (P := target) (thetaRuntime model.cells) (lower first second wiring)
    (encodeInput initial model.input) = Part.some (resultCodec model.cells out) ↔ _
  rw [observe_eq_numbered, Part.eq_some_iff, Part.mem_map_iff, Part.eq_some_iff]
  simp only [(resultCodec model.cells).injective.eq_iff, exists_eq_right]

theorem no_returns_iff_numbered (first : Graph P.args) (second : Graph Q.args)
    (wiring : Boundary.Wiring P.args Q.args) (model : EntryModel P) (initial : Heap model.cells) :
    (∀ raw, ¬ (lower first second wiring).Returns (thetaRuntime model.cells) (encodeInput initial model.input) raw) ↔
      numbered (RuntimeRoom.GeneratedProgram.lower first) (RuntimeRoom.GeneratedProgram.lower second)
        model (fun word => wiring.select word model.input) initial = Part.none := by
  rw [Part.eq_none_iff]
  constructor
  · intro absent out observed
    exact absent (resultCodec model.cells out)
      ((returns_iff_numbered first second wiring model initial out).mpr (Part.eq_some_iff.mpr observed))
  · intro absent raw returned
    obtain ⟨out, rfl⟩ := (resultCodec model.cells).surjective raw
    exact absent out (Part.eq_some_iff.mp ((returns_iff_numbered first second wiring model initial out).mp returned))

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Proofs
