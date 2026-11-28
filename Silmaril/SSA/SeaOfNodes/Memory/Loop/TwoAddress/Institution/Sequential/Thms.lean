module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.CellEmbedding.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Correctness

/-! Full results, absence, and disjoint heap framing of a sequential observation. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential

open RVSDG (Tuple)
open CellEmbedding (Embedding DisjointImages restrict result)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {cells leftCells rightCells : Nat} {P Q : EntrySignature}

theorem observe_eq_some_iff (first : Stage cells) (second : Word → Stage cells) (initial : Heap cells)
    (word nextWord : Word) (final : Heap cells) :
    observe first second initial = Part.some (word, nextWord, final) ↔
      ∃ middle, first initial = Part.some (word, middle) ∧ second word middle = Part.some (nextWord, final) :=
  Proofs.observe_eq_some_iff first second initial word nextWord final

/-- Sequential absence uses the second observer at the actual returned word and post-heap. -/
theorem observe_eq_none_iff (first : Stage cells) (second : Word → Stage cells) (initial : Heap cells) :
    observe first second initial = Part.none ↔
      first initial = Part.none ∨
        ∃ word middle, first initial = Part.some (word, middle) ∧ second word middle = Part.none :=
  Proofs.observe_eq_none_iff first second initial

theorem localObserve_eq_none_iff (e : Embedding leftCells cells) (f : Embedding rightCells cells)
    (left : Stage leftCells) (right : Word → Stage rightCells) (initial : Heap cells) :
    localObserve e f left right initial = Part.none ↔
      left (restrict e initial) = Part.none ∨
        ∃ word leftFinal, left (restrict e initial) = Part.some (word, leftFinal) ∧
          right word (restrict f initial) = Part.none :=
  Proofs.localObserve_eq_none_iff e f left right initial

/-- Factor observers with the ordinary heap-extension law through disjoint images. -/
theorem observe_eq_local (e : Embedding leftCells cells) (f : Embedding rightCells cells)
    (disjoint : DisjointImages e f) (first : Stage cells) (second : Word → Stage cells)
    (left : Stage leftCells) (right : Word → Stage rightCells)
    (firstFrame : ∀ heap, first heap = (left (restrict e heap)).map (result e heap))
    (secondFrame : ∀ word heap, second word heap = (right word (restrict f heap)).map (result f heap))
    (initial : Heap cells) :
    observe first second initial = localObserve e f left right initial :=
  Proofs.observe_eq_local e f disjoint first second left right firstFrame secondFrame initial

theorem numberedStage_embed (p : RuntimeRoom.GeneratedProgram P.args) (model : EntryModel P)
    (e : Embedding model.cells cells) (initial : Heap cells) :
    numberedStage p (embedModel model e) initial =
      (numberedStage p model (restrict e initial)).map (result e initial) :=
  Proofs.numberedStage_embed p model e initial

theorem colouredStage_eq_numbered (p : RuntimeRoom.GeneratedProgram P.args) (model : EntryModel P) :
    colouredStage p model = numberedStage p model :=
  Proofs.colouredStage_eq_numbered p model

theorem numberedStage_eq_some_iff (p : RuntimeRoom.GeneratedProgram P.args) (model : EntryModel P)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    numberedStage p model initial = Part.some (word, final) ↔
      p.observe model initial = Part.some (encodeResult word final) :=
  Proofs.numberedStage_eq_some_iff p model initial word final

theorem colouredStage_eq_some_iff (p : RuntimeRoom.GeneratedProgram P.args) (model : EntryModel P)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    colouredStage p model initial = Part.some (word, final) ↔
      p.Completes model initial (encodeResult word final) :=
  Proofs.colouredStage_eq_some_iff p model initial word final

theorem numbered_eq_local (first : RuntimeRoom.GeneratedProgram P.args)
    (second : RuntimeRoom.GeneratedProgram Q.args) (model : EntryModel P)
    (next : Word → Tuple (Val rightCells) Q.args) (e : Embedding model.cells cells)
    (f : Embedding rightCells cells) (disjoint : DisjointImages e f) (initial : Heap cells) :
    numbered first second (embedModel model e) (fun word => CellEmbedding.input f (next word)) initial =
      localObserve e f (numberedStage first model) (fun word => numberedStage second ⟨rightCells, next word⟩) initial :=
  Proofs.numbered_eq_local first second model next e f disjoint initial

theorem coloured_eq_numbered (first : RuntimeRoom.GeneratedProgram P.args)
    (second : RuntimeRoom.GeneratedProgram Q.args) (model : EntryModel P)
    (next : Word → Tuple (Val model.cells) Q.args) (initial : Heap model.cells) :
    coloured first second model next initial = numbered first second model next initial := by
  simp only [coloured, numbered, colouredStage_eq_numbered]

theorem coloured_eq_local (first : RuntimeRoom.GeneratedProgram P.args)
    (second : RuntimeRoom.GeneratedProgram Q.args) (model : EntryModel P)
    (next : Word → Tuple (Val rightCells) Q.args) (e : Embedding model.cells cells)
    (f : Embedding rightCells cells) (disjoint : DisjointImages e f) (initial : Heap cells) :
    coloured first second (embedModel model e) (fun word => CellEmbedding.input f (next word)) initial =
      localObserve e f (colouredStage first model) (fun word => colouredStage second ⟨rightCells, next word⟩) initial := by
  refine (coloured_eq_numbered first second (embedModel model e)
    (fun word => CellEmbedding.input f (next word)) initial).trans
    ((numbered_eq_local first second model next e f disjoint initial).trans ?_)
  simp only [colouredStage_eq_numbered]
  rfl

theorem numbered_eq_some_iff (first : RuntimeRoom.GeneratedProgram P.args)
    (second : RuntimeRoom.GeneratedProgram Q.args) (model : EntryModel P)
    (next : Word → Tuple (Val model.cells) Q.args) (initial : Heap model.cells)
    (word nextWord : Word) (final : Heap model.cells) :
    numbered first second model next initial = Part.some (word, nextWord, final) ↔
      ∃ middle, first.observe model initial = Part.some (encodeResult word middle) ∧
        second.observe ⟨model.cells, next word⟩ middle = Part.some (encodeResult nextWord final) := by
  simp only [numbered, observe_eq_some_iff, numberedStage_eq_some_iff]

/-- There are two finite firing witnesses. The second marking is initialized
from the first returned heap and the selected typed captures. -/
theorem coloured_eq_some_iff (first : RuntimeRoom.GeneratedProgram P.args)
    (second : RuntimeRoom.GeneratedProgram Q.args) (model : EntryModel P)
    (next : Word → Tuple (Val model.cells) Q.args) (initial : Heap model.cells)
    (word nextWord : Word) (final : Heap model.cells) :
    coloured first second model next initial = Part.some (word, nextWord, final) ↔
      ∃ middle, first.Completes model initial (encodeResult word middle) ∧
        second.Completes ⟨model.cells, next word⟩ middle (encodeResult nextWord final) := by
  simp only [coloured, observe_eq_some_iff, colouredStage_eq_some_iff]

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential
