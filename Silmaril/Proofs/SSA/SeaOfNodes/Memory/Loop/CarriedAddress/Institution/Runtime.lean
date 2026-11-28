module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Defs
import Silmaril.SSA.RVSDG.NestedTheta.Partial.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Petri.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Proofs

open RVSDG (Tuple)
open RVSDG.OrderedRuntime.Structured (Threaded)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P : EntrySignature} {cells : Nat}

private theorem encodeResult_surj (output : Tuple (WireVal cells) (Threaded wordPorts)) :
    ∃ word final, encodeResult word final = output :=
  match output with
  | .cons word (.cons final .nil) => ⟨word, final, rfl⟩

theorem runtimeObserve_eq_some_iff_native (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    runtimeObserve graph model initial = Part.some (encodeResult word final) ↔
      nativeReturns graph model initial word final := by
  let input := Petri.encodeArrival .entry initial model.input
  let output := encodeResult word final
  exact (RVSDG.NestedTheta.Partial.observe_ofRuntime_eq_some_iff_returns
    (thetaRuntime model.cells) (Petri.lower graph) input output).trans
    ((RVSDG.NestedTheta.Petri.finishes_iff _ _ _ _).symm.trans
      (Petri.lower_finishes_iff graph model.input initial word final))

theorem runtime_satisfaction (e : Equation P) (model : EntryModel P) :
    (∀ initial, runtimeObserve e.lhs model initial = runtimeObserve e.rhs model initial) ↔ e.Holds model := by
  constructor
  · intro equal initial word final
    change nativeReturns e.lhs model initial word final ↔ nativeReturns e.rhs model initial word final
    rw [← runtimeObserve_eq_some_iff_native, ← runtimeObserve_eq_some_iff_native, equal initial]
  · intro holds initial
    apply Part.ext
    intro output
    obtain ⟨word, final, rfl⟩ := encodeResult_surj output
    simpa only [← Part.eq_some_iff, runtimeObserve_eq_some_iff_native] using holds initial word final

theorem runtime_no_return_iff_native (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    runtimeObserve graph model initial = Part.none ↔ (nativeReturns graph model).NoReturn initial := by
  rw [Part.eq_none_iff]
  constructor
  · intro absent word final returned
    exact absent (encodeResult word final)
      (Part.eq_some_iff.mp ((runtimeObserve_eq_some_iff_native graph model initial word final).mpr returned))
  · intro absent output returned
    obtain ⟨word, final, rfl⟩ := encodeResult_surj output
    exact absent word final
      ((runtimeObserve_eq_some_iff_native graph model initial word final).mp (Part.eq_some_iff.mpr returned))

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Proofs
