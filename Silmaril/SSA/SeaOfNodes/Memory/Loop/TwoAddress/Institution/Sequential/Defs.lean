module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.CellEmbedding.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.PetriRoom.Defs

/-! Sequential partial observations of two separately emitted loops. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential

open RVSDG (Tuple)
open CellEmbedding (Embedding extend restrict)
open CarriedAddress.Institution.Backend (runtimeResult)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {cells leftCells rightCells : Nat} {P Q : EntrySignature}

abbrev Stage (cells : Nat) := Heap cells → Part (Word × Heap cells)
abbrev Result (cells : Nat) := Word × Word × Heap cells

/-- The second observer receives the first returned word and full post-heap.
The final observation keeps both words and the second returned heap. -/
def observe (first : Stage cells) (second : Word → Stage cells) (initial : Heap cells) : Part (Result cells) :=
  (first initial).bind fun (word, middle) =>
    (second word middle).map fun (nextWord, final) => (word, nextWord, final)

/-- The local factorization for disjoint images. The second valuation may
depend on the first return word. Its heap starts at the original restriction. -/
def localObserve (e : Embedding leftCells cells) (f : Embedding rightCells cells)
    (first : Stage leftCells) (second : Word → Stage rightCells) (initial : Heap cells) : Part (Result cells) :=
  (first (restrict e initial)).bind fun (word, leftFinal) =>
    (second word (restrict f initial)).map fun (nextWord, rightFinal) =>
      (word, nextWord, extend f (extend e initial leftFinal) rightFinal)

noncomputable def numberedStage (program : RuntimeRoom.GeneratedProgram P.args) (model : EntryModel P) :
    Stage model.cells :=
  fun initial => (program.observe model initial).map (runtimeResult model.cells).symm

noncomputable def colouredStage (program : RuntimeRoom.GeneratedProgram P.args) (model : EntryModel P) :
    Stage model.cells :=
  fun initial => (program.petriObserve model initial).map (runtimeResult model.cells).symm

/-- The selected next tuple is typed at the common ambient cell count. It
can use the first word and any captures fixed by the caller. -/
noncomputable def numbered (first : RuntimeRoom.GeneratedProgram P.args)
    (second : RuntimeRoom.GeneratedProgram Q.args) (model : EntryModel P)
    (next : Word → Tuple (Val model.cells) Q.args) (initial : Heap model.cells) : Part (Result model.cells) :=
  observe (numberedStage first model) (fun word => numberedStage second ⟨model.cells, next word⟩) initial

noncomputable def coloured (first : RuntimeRoom.GeneratedProgram P.args)
    (second : RuntimeRoom.GeneratedProgram Q.args) (model : EntryModel P)
    (next : Word → Tuple (Val model.cells) Q.args) (initial : Heap model.cells) : Part (Result model.cells) :=
  observe (colouredStage first model) (fun word => colouredStage second ⟨model.cells, next word⟩) initial

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential
