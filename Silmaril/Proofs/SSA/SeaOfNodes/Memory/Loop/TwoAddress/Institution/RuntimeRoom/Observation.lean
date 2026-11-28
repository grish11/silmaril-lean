module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Reindex.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Backend.Instances.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom.Proofs

open CategoryTheory
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open CarriedAddress.Institution.Backend (runtimeResult)

variable {P Q : EntrySignature}

theorem observe_eq_runtime (p : GeneratedProgram P.args) (model : EntryModel P) (initial : Heap model.cells) :
    p.observe model initial = runtimeObserve p.source model initial := by
  obtain ⟨_, _, rfl⟩ := p
  rfl

theorem observe_eq_some_iff_native (p : GeneratedProgram P.args) (model : EntryModel P)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    p.observe model initial = Part.some (encodeResult word final) ↔
      nativeReturns p.source model initial word final := by
  rw [observe_eq_runtime, runtimeObserve_eq_some_iff_native]

theorem observe_map (h : P ⟶ Q) (p : GeneratedProgram P.args) (model : EntryModel Q)
    (initial : Heap model.cells) :
    (p.map h).observe model initial = p.observe (reduct h model) initial := by
  apply Part.ext
  intro raw
  let value := (runtimeResult model.cells).symm raw
  have encoded : encodeResult value.1 value.2 = raw := (runtimeResult model.cells).apply_symm_apply raw
  rw [← encoded]
  exact (Part.eq_some_iff.symm.trans (observe_eq_some_iff_native (p.map h) model initial value.1 value.2)).trans
    ((nativeReturns_mapGraph h p.source model initial value.1 value.2).trans
      ((observe_eq_some_iff_native p (reduct h model) initial value.1 value.2).symm.trans Part.eq_some_iff))

theorem lower_source (s : Sentence P) : Sentence.lower s.source = s := by
  cases s with
  | equation lhs rhs =>
    obtain ⟨_, _, rfl⟩ := lhs
    obtain ⟨_, _, rfl⟩ := rhs
    rfl
  | terminates p =>
    obtain ⟨_, _, rfl⟩ := p
    rfl

theorem numbered_eq_translate (s : Sentence P) : s.numbered = translate s.source := by
  cases s with
  | equation lhs rhs => simp only [Sentence.numbered, Sentence.source, translate, lhs.generated, rhs.generated]
  | terminates p => simp only [Sentence.numbered, Sentence.source, translate, p.generated]

theorem satisfaction (s : Sentence P) (model : EntryModel P) : s.Holds model ↔ s.source.Holds model := by
  cases s <;> simp only [Sentence.Holds, Sentence.HoldsWith, Sentence.source, Institution.Sentence.Holds,
    Institution.Sentence.HoldsWith, observe_eq_runtime, runtimeObserve_eq_iff_native, runtimeObserve_dom_iff_native]

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom.Proofs
