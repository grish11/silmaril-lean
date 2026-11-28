module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.MemRefRoom.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeRoom.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.MemRefRoom.Proofs

open CategoryTheory
open RVSDG (Tuple)
open RVSDG.OrderedRuntime.Structured (Threaded)
open Silmaril.MLIR.MemRef (Buffer)
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q : EntrySignature} {cells : Nat}

private theorem returns_native (program : GeneratedProgram P.args) (model : EntryModel P)
    (initial : Buffer model.cells) (result : Word × Buffer model.cells) :
    program.Returns model initial result ↔
      nativeReturns program.source model initial.cell result.1 result.2.cell := by
  obtain ⟨graph, _, rfl⟩ := program
  obtain ⟨heap⟩ := initial
  obtain ⟨word, ⟨final⟩⟩ := result
  exact memrefReturns_iff_native graph model heap word final

private theorem encodeBufferResult_injective :
    Function.Injective (fun result : Word × Buffer cells => encodeResult result.1 result.2.cell) := by
  rintro ⟨leftWord, ⟨leftHeap⟩⟩ ⟨rightWord, ⟨rightHeap⟩⟩ equal
  exact Prod.ext (congrArg (fun output => output.get .head) equal)
    (congrArg Buffer.mk (congrArg (fun output => output.get (.tail .head)) equal))

private theorem encodeBufferResult_surjective (output : Tuple (WireVal cells) (Threaded wordPorts)) :
    ∃ result : Word × Buffer cells, encodeResult result.1 result.2.cell = output :=
  match output with
  | .cons word (.cons heap .nil) => ⟨(word, ⟨heap⟩), rfl⟩

theorem observe_eq_some_iff (program : GeneratedProgram P.args) (model : EntryModel P)
    (initial : Buffer model.cells) (result : Word × Buffer model.cells) :
    program.observe model initial = Part.some result ↔ program.Returns model initial result := by
  rw [Part.eq_some_iff]
  constructor
  · rintro ⟨witness, equal⟩
    exact equal ▸ Classical.choose_spec witness
  · intro returned
    let witness : ∃ r, program.Returns model initial r := ⟨result, returned⟩
    refine ⟨witness, ?_⟩
    change Classical.choose witness = result
    have actual := (returns_native program model initial _).mp (Classical.choose_spec witness)
    have expected := (returns_native program model initial _).mp returned
    have observed := (runtimeObserve_eq_some_iff_native program.source model initial.cell _ _).mpr actual
    have expectedObserved := (runtimeObserve_eq_some_iff_native program.source model initial.cell _ _).mpr expected
    exact encodeBufferResult_injective (Part.some_inj.mp (observed.symm.trans expectedObserved))

theorem observe_eq_some_iff_native (program : GeneratedProgram P.args) (model : EntryModel P)
    (initial : Buffer model.cells) (result : Word × Buffer model.cells) :
    program.observe model initial = Part.some result ↔
      nativeReturns program.source model initial.cell result.1 result.2.cell :=
  (observe_eq_some_iff program model initial result).trans (returns_native program model initial result)

theorem observe_eq_none_iff (program : GeneratedProgram P.args) (model : EntryModel P)
    (initial : Buffer model.cells) :
    program.observe model initial = Part.none ↔ (nativeReturns program.source model).NoReturn initial.cell := by
  rw [Part.eq_none_iff]
  constructor
  · intro absent word final returned
    exact absent (word, ⟨final⟩)
      (Part.eq_some_iff.mp ((observe_eq_some_iff_native program model initial (word, ⟨final⟩)).mpr returned))
  · rintro absent ⟨word, final⟩ returned
    exact absent word final.cell ((observe_eq_some_iff_native program model initial (word, final)).mp
      (Part.eq_some_iff.mpr returned))

theorem observe_map (h : P ⟶ Q) (program : GeneratedProgram P.args)
    (model : EntryModel Q) (initial : Buffer model.cells) :
    (program.map h).observe model initial = program.observe (reduct h model) initial := by
  apply Part.ext
  intro result
  exact (Part.eq_some_iff.symm.trans (observe_eq_some_iff_native _ model initial result)).trans
    ((nativeReturns_mapGraph h program.source model initial.cell result.1 result.2.cell).trans
      ((observe_eq_some_iff_native program (reduct h model) initial result).symm.trans Part.eq_some_iff))

theorem observe_runtime (graph : Graph P.args) (model : EntryModel P) (initial : Buffer model.cells) :
    ((GeneratedProgram.lower graph).observe model initial).map (fun result => encodeResult result.1 result.2.cell) =
      RuntimeEntry.observe graph (RuntimeRoom.modelEntry model initial.cell).val := by
  apply Part.ext
  intro output
  obtain ⟨result, rfl⟩ := encodeBufferResult_surjective output
  rw [Part.mem_map_iff]
  have runtime := RuntimeEntry.observe_eq_some_iff_native graph
    (RuntimeEntry.decode_encode ⟨model.input, initial.cell⟩) result.1 result.2.cell
  constructor
  · rintro ⟨observed, member, equal⟩
    have same : observed = result := encodeBufferResult_injective equal
    subst observed
    exact Part.eq_some_iff.mp (runtime.mpr
      ((observe_eq_some_iff_native _ _ _ _).mp (Part.eq_some_iff.mpr member)))
  · intro member
    have returned := runtime.mp
      (Part.eq_some_iff.mpr member)
    exact ⟨result, Part.eq_some_iff.mp ((observe_eq_some_iff_native _ _ _ _).mpr returned), rfl⟩

theorem satisfaction (e : Equation P) (model : EntryModel P) :
    (lowerEquation e).Holds model ↔ e.Holds model := by
  constructor
  · intro holds initial word final
    let result := (word, Buffer.mk final)
    have equal := iff_of_eq (congrArg (· = Part.some result) (holds ⟨initial⟩))
    exact (observe_eq_some_iff_native (GeneratedProgram.lower e.lhs) model ⟨initial⟩ result).symm.trans
      (equal.trans (observe_eq_some_iff_native (GeneratedProgram.lower e.rhs) model ⟨initial⟩ result))
  · intro holds initial
    apply Part.ext
    intro result
    exact (Part.eq_some_iff.symm.trans
      (observe_eq_some_iff_native (GeneratedProgram.lower e.lhs) model initial result)).trans
      ((holds initial.cell result.1 result.2.cell).trans
        ((observe_eq_some_iff_native (GeneratedProgram.lower e.rhs) model initial result).symm.trans Part.eq_some_iff))

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.MemRefRoom.Proofs
