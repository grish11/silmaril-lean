module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Boundary.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Thms
import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Splice.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Proofs

open RVSDG (Tuple)
open RVSDG.NestedTheta.Institution
open RVSDG.NestedTheta.ExplicitRuntime.Splice (graph_observe)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open Memory.Diamond.Institution (PortMap pullInput)
open CarriedAddress.Institution.Backend (runtimeResult)

variable {next last : List ValueSort} {cells : Nat} {P Q R : EntrySignature}

set_option backward.isDefEq.respectTransparency false

private theorem pull_under {args : List ValueSort} {sort : ValueSort} (head : Val cells sort)
    (input : Tuple (Val cells) next) (ports : PortMap args next) :
    pullInput (fun p => .tail (ports p)) (Tuple.cons (F := Val cells) head input) = pullInput ports input := by
  induction args with
  | nil => rfl
  | cons _ _ ih => simp only [pullInput, ih]; rfl

private theorem pull_identity (input : Tuple (Val cells) next) :
    pullInput (fun p => p) input = input := by
  induction input with
  | nil => rfl
  | cons _ _ ih =>
    simp only [pullInput, Tuple.get]
    rw [pull_under, ih]

private theorem carryFirst_select (wiring : Boundary.Wiring next last) (first second : Word)
    (input : Tuple (Val cells) next) :
    (carryFirst wiring).select second (.cons (t := .word) first input) =
      .cons (t := .word) first (wiring.select second input) := by
  change Tuple.cons (F := Val cells) (t := .word) first
    ((wiring.map fun p => .tail p).select second (Tuple.cons (F := Val cells) (t := ValueSort.word) first input)) = _
  rw [Boundary.Wiring.select_map, pull_under, pull_identity]

private theorem lastTwo_observe (second : Graph next) (third : Graph last) (wiring : Boundary.Wiring next last)
    (firstWord : Word) (input : Tuple (Val cells) next) (initial : Heap cells) :
    RuntimeObservation.observe (P := target) (thetaRuntime cells) (lastTwo second third wiring)
        (Boundary.packet firstWord input initial) =
      (RuntimeObservation.observe (P := target) (thetaRuntime cells) (Petri.lower second)
        (encodeInput initial input)).bind fun
      | .cons secondWord (.cons middle .nil) =>
        (RuntimeObservation.observe (P := target) (thetaRuntime cells) (Petri.lower third)
          (encodeInput middle (wiring.select secondWord input))).map (Wrapper.thirdOutput firstWord secondWord) := by
  unfold lastTwo RuntimeObservation.observe
  rw [graph_observe]
  change (RuntimeObservation.observe (P := target) (thetaRuntime cells)
    (Wrapper.forwarding second (fun p => .tail p)) (Boundary.packet firstWord input initial)).bind
    (RuntimeObservation.observe (P := target) (thetaRuntime cells) (finalStage third wiring)) = _
  rw [Boundary.packet, Wrapper.forwarding_observe, pull_under, pull_identity, Part.bind_map]
  congr 1
  funext out
  cases out with
  | cons word rest =>
    cases rest with
    | cons heap tail =>
      cases tail
      rw [Wrapper.producerOutput, finalStage, Boundary.splice_observe, carryFirst_select, Wrapper.third_observe]
      rfl

theorem observe_eq_numbered (first : Graph P.args) (second : Graph Q.args) (third : Graph R.args)
    (firstWiring : Boundary.Wiring P.args Q.args) (secondWiring : Boundary.Wiring Q.args R.args)
    (model : EntryModel P) (initial : Heap model.cells) :
    RuntimeObservation.observe (P := target) (thetaRuntime model.cells)
        (lower first second third firstWiring secondWiring) (encodeInput initial model.input) =
      (numbered first second third firstWiring secondWiring model initial).map (resultCodec model.cells) := by
  unfold lower RuntimeObservation.observe
  rw [graph_observe]
  change (RuntimeObservation.observe (P := target) (thetaRuntime model.cells) (Wrapper.producer first)
      (encodeInput initial model.input)).bind
      (RuntimeObservation.observe (P := target) (thetaRuntime model.cells)
        (Boundary.splice firstWiring (lastTwoChecked second third secondWiring))) = _
  rw [Wrapper.producer_observe, Part.bind_map]
  simp only [numbered, Sequential.numbered, Sequential.observe, numberedStage, Part.bind_map,
    Part.map_bind, Part.map_map, Part.bind_assoc]
  congr 1
  funext out
  cases out with
  | cons word rest =>
    cases rest with
    | cons heap tail =>
      cases tail
      rw [Wrapper.producerOutput, Boundary.splice_observe, lastTwo_observe]
      congr 1
      funext nextOut
      cases nextOut with
      | cons nextWord rest =>
        cases rest with
        | cons nextHeap tail =>
          cases tail
          rfl

theorem observe_eq_linked_pair (first : Graph P.args) (second : Graph Q.args) (third : Graph R.args)
    (firstWiring : Boundary.Wiring P.args Q.args) (secondWiring : Boundary.Wiring Q.args R.args)
    (model : EntryModel P) (initial : Heap model.cells) :
    RuntimeObservation.observe (P := target) (thetaRuntime model.cells)
        (lower first second third firstWiring secondWiring) (encodeInput initial model.input) =
      (RuntimeObservation.observe (P := target) (thetaRuntime model.cells)
        (Linked.lower first second firstWiring) (encodeInput initial model.input)).bind fun output =>
        let (firstWord, secondWord, middle) := (Linked.resultCodec model.cells).symm output
        let bank := secondWiring.select secondWord (firstWiring.select firstWord model.input)
        (numberedStage (P := R) (.lower third) ⟨model.cells, bank⟩ middle).map fun (word, final) =>
          resultCodec model.cells (firstWord, secondWord, word, final) := by
  rw [observe_eq_numbered, Linked.observe_eq_numbered]
  simp only [numbered, Part.map_bind, Part.bind_map, Part.map_map, Equiv.symm_apply_apply]
  rfl

theorem returns_iff_numbered (first : Graph P.args) (second : Graph Q.args) (third : Graph R.args)
    (firstWiring : Boundary.Wiring P.args Q.args) (secondWiring : Boundary.Wiring Q.args R.args)
    (model : EntryModel P) (initial : Heap model.cells) (out : Result model.cells) :
    (lower first second third firstWiring secondWiring).Returns (thetaRuntime model.cells)
        (encodeInput initial model.input) (resultCodec model.cells out) ↔
      numbered first second third firstWiring secondWiring model initial = Part.some out := by
  rw [← RVSDG.NestedTheta.Partial.observe_ofRuntime_eq_some_iff_returns]
  change RuntimeObservation.observe (P := target) (thetaRuntime model.cells)
    (lower first second third firstWiring secondWiring) (encodeInput initial model.input) =
      Part.some (resultCodec model.cells out) ↔ _
  rw [observe_eq_numbered, Part.eq_some_iff, Part.mem_map_iff, Part.eq_some_iff]
  simp only [(resultCodec model.cells).injective.eq_iff, exists_eq_right]

theorem numbered_eq_some_iff (first : Graph P.args) (second : Graph Q.args) (third : Graph R.args)
    (firstWiring : Boundary.Wiring P.args Q.args) (secondWiring : Boundary.Wiring Q.args R.args)
    (model : EntryModel P) (initial final : Heap model.cells) (firstWord secondWord thirdWord : Word) :
    numbered first second third firstWiring secondWiring model initial =
        Part.some (firstWord, secondWord, thirdWord, final) ↔
      ∃ firstHeap secondHeap,
        (Petri.lower first).Returns (thetaRuntime model.cells) (encodeInput initial model.input)
          (encodeResult firstWord firstHeap) ∧
        (Petri.lower second).Returns (thetaRuntime model.cells)
          (encodeInput firstHeap (firstWiring.select firstWord model.input)) (encodeResult secondWord secondHeap) ∧
        (Petri.lower third).Returns (thetaRuntime model.cells)
          (encodeInput secondHeap (secondWiring.select secondWord (firstWiring.select firstWord model.input)))
          (encodeResult thirdWord final) := by
  simp only [numbered, Part.eq_some_iff, Part.mem_bind_iff, Part.mem_map_iff]
  have stage (p : Graph R.args) (bank : Tuple (Val model.cells) R.args) (heap result : Heap model.cells)
      (word : Word) : (word, result) ∈ numberedStage (P := R) (.lower p) ⟨model.cells, bank⟩ heap ↔
        (Petri.lower p).Returns (thetaRuntime model.cells) (encodeInput heap bank) (encodeResult word result) := by
    rw [← Part.eq_some_iff, numberedStage_eq_some_iff, ← RVSDG.NestedTheta.Partial.observe_ofRuntime_eq_some_iff_returns]
    rfl
  constructor
  · rintro ⟨⟨firstOut, secondOut, secondHeap⟩, pair, ⟨⟨thirdOut, thirdHeap⟩, finished, equal⟩⟩
    cases equal
    have stages := (Sequential.numbered_eq_some_iff (.lower first) (.lower second) model
      (fun word => firstWiring.select word model.input) initial firstOut secondOut secondHeap).mp
      (Part.eq_some_iff.mpr pair)
    obtain ⟨firstHeap, left, right⟩ := stages
    exact ⟨firstHeap, secondHeap, (RVSDG.NestedTheta.Partial.observe_ofRuntime_eq_some_iff_returns _ _ _ _).mp left,
      (RVSDG.NestedTheta.Partial.observe_ofRuntime_eq_some_iff_returns _ _ _ _).mp right, (stage _ _ _ _ _).mp finished⟩
  · rintro ⟨firstHeap, secondHeap, left, right, finished⟩
    refine ⟨(firstWord, secondWord, secondHeap), ?_, (thirdWord, final), (stage _ _ _ _ _).mpr finished, rfl⟩
    apply Part.eq_some_iff.mp
    apply (Sequential.numbered_eq_some_iff (.lower first) (.lower second) model
      (fun word => firstWiring.select word model.input) initial firstWord secondWord secondHeap).mpr
    exact ⟨firstHeap, (RVSDG.NestedTheta.Partial.observe_ofRuntime_eq_some_iff_returns _ _ _ _).mpr left,
      (RVSDG.NestedTheta.Partial.observe_ofRuntime_eq_some_iff_returns _ _ _ _).mpr right⟩

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Proofs
