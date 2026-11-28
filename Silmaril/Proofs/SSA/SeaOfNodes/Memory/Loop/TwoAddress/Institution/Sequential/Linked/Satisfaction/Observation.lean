module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Boundary.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.MemRef.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Partial.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.Proofs

open CategoryTheory
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q : EntrySignature}

set_option backward.isDefEq.respectTransparency false

theorem sequential_eq_some_iff (p : Program P) (model : EntryModel P) (initial : Heap model.cells)
    (out : Result model.cells) :
    p.sequentialObserve model initial = Part.some out ↔ p.nativeReturns model initial out := by
  obtain ⟨word, nextWord, final⟩ := out
  rw [Program.sequentialObserve, Sequential.numbered_eq_some_iff]
  simp only [RuntimeRoom.GeneratedProgram.observe_eq_some_iff_native, RuntimeRoom.GeneratedProgram.lower,
    Program.nativeReturns]

theorem numbered_eq_some_iff (p : Program P) (model : EntryModel P) (initial : Heap model.cells)
    (out : Result model.cells) :
    p.numberedObserve model initial = Part.some (resultCodec model.cells out) ↔ p.nativeReturns model initial out :=
  (RVSDG.NestedTheta.Partial.observe_ofRuntime_eq_some_iff_returns (thetaRuntime model.cells) p.emitNumbered.graph _ _).trans
    ((Linked.returns_iff_numbered p.first p.second p.wiring model initial out).trans
      (sequential_eq_some_iff p model initial out))

theorem memref_returns_iff (p : Program P) (model : EntryModel P) (initial : Heap model.cells)
    (out : Result model.cells) : p.memrefReturns model initial out ↔ p.nativeReturns model initial out := by
  obtain ⟨word, nextWord, final⟩ := out
  exact (Linked.MemRef.returns_iff_numbered p.first p.second p.wiring model initial word nextWord final).trans
    ((RVSDG.NestedTheta.Partial.observe_ofRuntime_eq_some_iff_returns (thetaRuntime model.cells)
      p.emitNumbered.graph _ _).symm.trans (numbered_eq_some_iff p model initial (word, nextWord, final)))

theorem coloured_returns_iff (p : Program P) (model : EntryModel P) (initial : Heap model.cells)
    (out : Result model.cells) : p.colouredReturns model initial out ↔ p.nativeReturns model initial out :=
  (RVSDG.NestedTheta.Petri.finishes_iff _ _ _ _).trans
    ((RVSDG.NestedTheta.Partial.observe_ofRuntime_eq_some_iff_returns (thetaRuntime model.cells)
      p.emitNumbered.graph _ _).symm.trans (numbered_eq_some_iff p model initial out))

theorem native_returns_map (h : P ⟶ Q) (p : Program P) (model : EntryModel Q)
    (initial : Heap model.cells) (out : Result model.cells) :
    (p.map h).nativeReturns model initial out ↔ p.nativeReturns (reduct h model) initial out := by
  obtain ⟨word, nextWord, final⟩ := out
  simp only [Program.nativeReturns, Program.map, nativeReturns_mapGraph]
  rw [p.wiring.select_map (EntrySignature.Hom.port h) word model.input]
  rfl

theorem numbered_observe_map (h : P ⟶ Q) (p : Program P) (model : EntryModel Q) (initial : Heap model.cells) :
    (p.map h).numberedObserve model initial = p.numberedObserve (reduct h model) initial := by
  apply Part.ext
  intro raw
  obtain ⟨out, rfl⟩ := (resultCodec model.cells).surjective raw
  exact Part.eq_some_iff.symm.trans ((numbered_eq_some_iff (p.map h) model initial out).trans
    ((native_returns_map h p model initial out).trans
      ((numbered_eq_some_iff p (reduct h model) initial out).symm.trans Part.eq_some_iff)))

theorem numbered_agrees (p q : Program P) (model : EntryModel P) :
    (∀ initial, p.numberedObserve model initial = q.numberedObserve model initial) ↔
      Agrees (p.nativeReturns model) (q.nativeReturns model) := by
  constructor
  · intro agree initial out
    exact (numbered_eq_some_iff p model initial out).symm.trans
      ((iff_of_eq (congrArg (· = Part.some (resultCodec model.cells out)) (agree initial))).trans
        (numbered_eq_some_iff q model initial out))
  · intro agree initial
    apply Part.ext
    intro raw
    obtain ⟨out, rfl⟩ := (resultCodec model.cells).surjective raw
    simpa only [← Part.eq_some_iff, numbered_eq_some_iff] using agree initial out

theorem numbered_dom (p : Program P) (model : EntryModel P) (initial : Heap model.cells) :
    (p.numberedObserve model initial).Dom ↔ ∃ out, p.nativeReturns model initial out := by
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨raw, observed⟩
    obtain ⟨out, rfl⟩ := (resultCodec model.cells).surjective raw
    exact ⟨out, (numbered_eq_some_iff p model initial out).mp (Part.eq_some_iff.mpr observed)⟩
  · rintro ⟨out, returned⟩
    exact ⟨resultCodec model.cells out, Part.eq_some_iff.mp ((numbered_eq_some_iff p model initial out).mpr returned)⟩

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.Proofs
