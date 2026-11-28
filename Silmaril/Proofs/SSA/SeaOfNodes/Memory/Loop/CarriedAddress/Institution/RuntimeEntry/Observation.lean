module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeEntry.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeEntry.Codec

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeEntry.Proofs

open CategoryTheory
open RVSDG (Tuple)
open RVSDG.OrderedRuntime.Structured (Threaded)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q : EntrySignature} {cells : Nat}

theorem observe_eq_some_iff_native (graph : Graph P.args) {raw : RawEntry P.args cells}
    {entry : Entry P.args cells} (decoded : decode raw = some entry) (word : Word) (final : Heap cells) :
    observe graph raw = Part.some (encodeResult word final) ↔
      nativeReturns graph entry.model entry.heap word final := by
  rw [← (decode_eq_some_iff raw entry).mp decoded]
  exact runtimeObserve_eq_some_iff_native graph entry.model entry.heap word final

theorem observe_eq_none_iff_native (graph : Graph P.args) {raw : RawEntry P.args cells}
    {entry : Entry P.args cells} (decoded : decode raw = some entry) :
    observe graph raw = Part.none ↔ (nativeReturns graph entry.model).NoReturn entry.heap := by
  rw [← (decode_eq_some_iff raw entry).mp decoded]
  exact runtime_no_return_iff_native graph entry.model entry.heap

private theorem encodeResult_surjective (output : Tuple (WireVal cells) (Threaded wordPorts)) :
    ∃ word final, encodeResult word final = output :=
  match output with
  | .cons word (.cons final .nil) => ⟨word, final, rfl⟩

theorem observe_mapGraph (h : P ⟶ Q) (graph : Graph P.args) (raw : RawEntry Q.args cells)
    (entered : Admissible raw) :
    observe (mapGraph h graph) raw = observe graph (reindex h raw) := by
  obtain ⟨entry, rfl⟩ := (admissible_iff_exists_encode raw).mp entered
  rw [reindex_encode]
  apply Part.ext
  intro output
  obtain ⟨word, final, rfl⟩ := encodeResult_surjective output
  simp only [← Part.eq_some_iff, observe_eq_some_iff_native _ (decode_encode _)]
  exact nativeReturns_mapGraph h graph entry.model entry.heap word final

theorem satisfaction (e : Equation P) (cells : Nat) :
    Holds e cells ↔ ∀ input : Tuple (Val cells) P.args, e.Holds (⟨cells, input⟩ : EntryModel P) := by
  constructor
  · intro holds input
    apply (runtime_satisfaction e ⟨cells, input⟩).mp
    intro heap
    exact holds (Entry.encode ⟨input, heap⟩) rfl
  · intro holds raw admissible
    obtain ⟨entry, rfl⟩ := (admissible_iff_exists_encode raw).mp admissible
    exact (runtime_satisfaction e entry.model).mpr (holds entry.input) entry.heap

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeEntry.Proofs
