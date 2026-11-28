module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeEntry.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Backend.Instances.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.MemRef.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Petri.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Partial.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Proofs

open CategoryTheory
open RVSDG (Tuple)
open RVSDG.NestedTheta.Institution
open RVSDG.NestedTheta.Partial (observe_ofRuntime_eq_some_iff_returns)
open RVSDG.OrderedRuntime.Structured (Threaded)
open CarriedAddress.Institution (Observation)
open CarriedAddress.Institution.Backend (runtimeResult)
open CarriedAddress.Institution.RuntimeEntry (decodePayload encode_decodePayload)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P : EntrySignature} {cells : Nat}

theorem memrefReturns_iff_native (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    memrefReturns graph model initial word final ↔ nativeReturns graph model initial word final :=
  MemRef.returns_iff graph model.input initial word final

theorem petriReturns_iff_native (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    petriReturns graph model initial word final ↔ nativeReturns graph model initial word final :=
  Petri.lower_finishes_iff graph model.input initial word final

theorem runtimeObserve_eq_some_iff_native (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    runtimeObserve graph model initial = Part.some (encodeResult word final) ↔
      nativeReturns graph model initial word final := by
  let runtime := thetaRuntime model.cells
  let program := Petri.lower graph
  let input := encodeInput initial model.input
  let output := encodeResult word final
  exact (observe_ofRuntime_eq_some_iff_returns runtime program input output).trans
    ((RVSDG.NestedTheta.Petri.finishes_iff runtime program input output).symm.trans
      (petriReturns_iff_native graph model initial word final))

private theorem output_image (output : Tuple (WireVal cells) (Threaded wordPorts)) :
    ∃ word final, encodeResult word final = output := by
  let result := (runtimeResult cells).symm output
  exact ⟨result.1, result.2, (runtimeResult cells).apply_symm_apply output⟩

theorem runtimeObserve_eq_iff_native (lhs rhs : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    runtimeObserve lhs model initial = runtimeObserve rhs model initial ↔
      ∀ word final, nativeReturns lhs model initial word final ↔ nativeReturns rhs model initial word final := by
  constructor
  · intro equal word final
    rw [← runtimeObserve_eq_some_iff_native, ← runtimeObserve_eq_some_iff_native, equal]
  · intro agrees
    apply Part.ext
    intro output
    obtain ⟨word, final, rfl⟩ := output_image output
    simpa only [← Part.eq_some_iff, runtimeObserve_eq_some_iff_native] using agrees word final

theorem runtimeObserve_dom_iff_native (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) :
    (runtimeObserve graph model initial).Dom ↔ ∃ word final, nativeReturns graph model initial word final := by
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨output, observed⟩
    obtain ⟨word, final, rfl⟩ := output_image output
    exact ⟨word, final, (runtimeObserve_eq_some_iff_native graph model initial word final).mp
      (Part.eq_some_iff.mpr observed)⟩
  · rintro ⟨word, final, returned⟩
    exact ⟨encodeResult word final, Part.eq_some_iff.mp
      ((runtimeObserve_eq_some_iff_native graph model initial word final).mpr returned)⟩

theorem runtimeObserve_eq_none_iff_native (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) :
    runtimeObserve graph model initial = Part.none ↔ (nativeReturns graph model).NoReturn initial := by
  simp only [Part.eq_none_iff', runtimeObserve_dom_iff_native, Observation.NoReturn, not_exists]

private theorem forall_payload {args : List ValueSort} (test : Tuple (WireVal cells) (carrier args) → Prop) :
    (∀ raw, test raw) ↔ ∀ (input : Tuple (Val cells) args) (heap : Heap cells), test (encodeInput heap input) := by
  constructor
  · intro all input heap
    exact all (encodeInput heap input)
  · intro all raw
    let entry := decodePayload raw
    exact (encode_decodePayload raw) ▸ all entry.input entry.heap

theorem numbered_satisfaction (s : Sentence P) (cells : Nat) :
    (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime cells)) (translate s) ↔
      s.HoldsAt cells := by
  cases s with
  | equation lhs rhs =>
    change (∀ raw, RuntimeObservation.observe (thetaRuntime cells) (lowerProgram lhs).graph raw =
      RuntimeObservation.observe (thetaRuntime cells) (lowerProgram rhs).graph raw) ↔ _
    exact (forall_payload (cells := cells) (args := P.args) (fun raw =>
      RuntimeObservation.observe (thetaRuntime cells) (lowerProgram lhs).graph raw =
        RuntimeObservation.observe (thetaRuntime cells) (lowerProgram rhs).graph raw)).trans
      (forall_congr' fun input => forall_congr' fun heap => runtimeObserve_eq_iff_native lhs rhs ⟨cells, input⟩ heap)
  | terminates graph =>
    change (∀ raw, (RuntimeObservation.observe (thetaRuntime cells) (lowerProgram graph).graph raw).Dom) ↔ _
    exact (forall_payload (cells := cells) (args := P.args) (fun raw =>
      (RuntimeObservation.observe (thetaRuntime cells) (lowerProgram graph).graph raw).Dom)).trans
      (forall_congr' fun input => forall_congr' fun heap => runtimeObserve_dom_iff_native graph ⟨cells, input⟩ heap)

theorem memref_satisfaction (s : Sentence P) (model : EntryModel P) :
    s.HoldsWith (memrefReturns · model) ↔ s.Holds model := by
  cases s <;> simp only [Sentence.Holds, Sentence.HoldsWith, memrefReturns_iff_native]

theorem petri_satisfaction (s : Sentence P) (model : EntryModel P) :
    s.HoldsWith (petriReturns · model) ↔ s.Holds model := by
  cases s <;> simp only [Sentence.Holds, Sentence.HoldsWith, petriReturns_iff_native]

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Proofs
