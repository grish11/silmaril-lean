module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.CellRelabel.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.MemRefRoom.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.CellRelabel.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.MemRefRoom.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.CellRelabelProofs

open CellRelabel (Permutation heap)
open Silmaril.MLIR.MemRef (Buffer)
open CarriedAddress.Institution.Backend (runtimeResult)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

set_option backward.isDefEq.respectTransparency false

variable {P : EntrySignature}

theorem nativeReturns_relabel (graph : Graph P.args) (model : EntryModel P) (σ : Permutation model.cells)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    nativeReturns graph (relabelModel model σ) (heap σ initial) word (heap σ final) ↔
      nativeReturns graph model initial word final :=
  graph.returns_relabel σ model.input initial word final

theorem holds_relabel (s : Sentence P) (model : EntryModel P) (σ : Permutation model.cells) :
    s.Holds (relabelModel model σ) ↔ s.Holds model := by
  cases s with
  | equation lhs rhs =>
    constructor
    · intro holds initial word final
      exact (nativeReturns_relabel lhs model σ initial word final).symm.trans
        ((holds (heap σ initial) word (heap σ final)).trans (nativeReturns_relabel rhs model σ initial word final))
    · intro holds initial word final
      obtain ⟨oldInitial, rfl⟩ := (heap σ).surjective initial
      obtain ⟨oldFinal, rfl⟩ := (heap σ).surjective final
      exact (nativeReturns_relabel lhs model σ oldInitial word oldFinal).trans
        ((holds oldInitial word oldFinal).trans (nativeReturns_relabel rhs model σ oldInitial word oldFinal).symm)
  | terminates graph =>
    constructor
    · intro holds initial
      obtain ⟨word, final, returned⟩ := holds (heap σ initial)
      obtain ⟨oldFinal, rfl⟩ := (heap σ).surjective final
      exact ⟨word, oldFinal, (nativeReturns_relabel graph model σ initial word oldFinal).mp returned⟩
    · intro holds initial
      obtain ⟨oldInitial, rfl⟩ := (heap σ).surjective initial
      obtain ⟨word, final, returned⟩ := holds oldInitial
      exact ⟨word, heap σ final, (nativeReturns_relabel graph model σ oldInitial word final).mpr returned⟩

theorem observe_relabel (p : RuntimeRoom.GeneratedProgram P.args) (model : EntryModel P)
    (σ : Permutation model.cells) (initial : Heap model.cells) :
    p.observe (relabelModel model σ) (heap σ initial) =
      (p.observe model initial).map (relabelOutput σ) := by
  apply Part.ext
  intro raw
  obtain ⟨before, rfl⟩ := (relabelOutput σ).surjective raw
  obtain ⟨⟨word, final⟩, rfl⟩ := (runtimeResult model.cells).surjective before
  let output := encodeResult word final
  calc
    relabelOutput σ output ∈ p.observe (relabelModel model σ) (heap σ initial) ↔
        nativeReturns p.source (relabelModel model σ) (heap σ initial) word (heap σ final) :=
      Part.eq_some_iff.symm.trans
        (p.observe_eq_some_iff_native (relabelModel model σ) (heap σ initial) word (heap σ final))
    _ ↔ nativeReturns p.source model initial word final := nativeReturns_relabel p.source model σ initial word final
    _ ↔ output ∈ p.observe model initial :=
      (p.observe_eq_some_iff_native model initial word final).symm.trans Part.eq_some_iff
    _ ↔ relabelOutput σ output ∈ (p.observe model initial).map (relabelOutput σ) := by
      rw [Part.mem_map_iff]
      constructor
      · intro observed
        exact ⟨output, observed, rfl⟩
      · rintro ⟨before, observed, equal⟩
        exact (relabelOutput σ).injective equal ▸ observed

theorem memRef_returns_relabel (p : MemRefRoom.GeneratedProgram P.args) (model : EntryModel P)
    (σ : Permutation model.cells) (initial : Buffer model.cells) (word : Word) (final : Buffer model.cells) :
    p.Returns (relabelModel model σ) ⟨heap σ initial.cell⟩ (word, ⟨heap σ final.cell⟩) ↔
      p.Returns model initial (word, final) :=
  (p.returns_iff_native (relabelModel model σ) ⟨heap σ initial.cell⟩ word ⟨heap σ final.cell⟩).trans
    ((nativeReturns_relabel p.source model σ initial.cell word final.cell).trans
      (p.returns_iff_native model initial word final).symm)

theorem memRef_no_return_relabel (p : MemRefRoom.GeneratedProgram P.args) (model : EntryModel P)
    (σ : Permutation model.cells) (initial : Buffer model.cells) :
    (∀ word final, ¬ p.Returns (relabelModel model σ) ⟨heap σ initial.cell⟩ (word, final)) ↔
      ∀ word final, ¬ p.Returns model initial (word, final) := by
  constructor
  · intro absent word ⟨final⟩ returned
    exact absent word ⟨heap σ final⟩ ((memRef_returns_relabel p model σ initial word ⟨final⟩).mpr returned)
  · intro absent word ⟨final⟩ returned
    obtain ⟨oldFinal, rfl⟩ := (heap σ).surjective final
    exact absent word ⟨oldFinal⟩ ((memRef_returns_relabel p model σ initial word ⟨oldFinal⟩).mp returned)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.CellRelabelProofs
