module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.PetriRoom.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Backend.Instances.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.PetriRoom.Proofs

open RVSDG (Tuple)
open RVSDG.OrderedRuntime.Structured (Threaded)
open RuntimeRoom (GeneratedProgram)
open CarriedAddress.Institution.Backend (runtimeResult)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P : EntrySignature}

theorem completes_iff_numbered (p : GeneratedProgram P.args) (model : EntryModel P)
    (initial : Heap model.cells) (output : Tuple (WireVal model.cells) (Threaded wordPorts)) :
    p.Completes model initial output ↔ p.observe model initial = Part.some output := by
  let value := (runtimeResult model.cells).symm output
  have encoded : encodeResult value.1 value.2 = output := (runtimeResult model.cells).apply_symm_apply output
  rw [← encoded]
  have linked : p.Completes model initial (encodeResult value.1 value.2) ↔
      petriReturns p.source model initial value.1 value.2 := by
    obtain ⟨_, _, rfl⟩ := p
    rfl
  exact linked.trans ((petriReturns_iff_native p.source model initial value.1 value.2).trans
    (p.observe_eq_some_iff_native model initial value.1 value.2).symm)

theorem petriObserve_eq_numbered (p : GeneratedProgram P.args) (model : EntryModel P)
    (initial : Heap model.cells) : p.petriObserve model initial = p.observe model initial := by
  apply Part.ext
  intro output
  constructor
  · rintro ⟨witness, rfl⟩
    exact Part.eq_some_iff.mp ((completes_iff_numbered p model initial _).mp (Classical.choose_spec witness))
  · intro observed
    have witness : ∃ result, p.Completes model initial result :=
      ⟨output, (completes_iff_numbered p model initial output).mpr (Part.eq_some_iff.mpr observed)⟩
    have chosen := (completes_iff_numbered p model initial _).mp (Classical.choose_spec witness)
    exact ⟨witness, Part.some_injective (chosen.symm.trans (Part.eq_some_iff.mpr observed))⟩

theorem holds_iff_numbered (s : RuntimeRoom.Sentence P) (model : EntryModel P) :
    Holds s model ↔ s.Holds model := by
  cases s <;> simp only [Holds, RuntimeRoom.Sentence.Holds, RuntimeRoom.Sentence.HoldsWith,
    petriObserve_eq_numbered]

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.PetriRoom.Proofs
