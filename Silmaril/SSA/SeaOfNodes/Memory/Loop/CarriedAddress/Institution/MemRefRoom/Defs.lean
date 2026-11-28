module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Defs

/-! Generated ordered MemRef equations at the initialized root boundary. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.MemRefRoom

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.MLIR.MemRef (Buffer)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q : EntrySignature} {args : List ValueSort}

/-- The sentence has an emitted CFG at each model's cell count. The
source supplies the typed address choices used by the block interpreter
and the data needed to re-emit the CFG. -/
structure GeneratedProgram (args : List ValueSort) where
  source : Graph args
  cfg : (cells : Nat) → MemRef.Program cells args
  generated : cfg = fun cells => MemRef.lower cells source

def GeneratedProgram.lower (graph : Graph args) : GeneratedProgram args :=
  ⟨graph, fun cells => MemRef.lower cells graph, rfl⟩

def GeneratedProgram.map (h : P ⟶ Q) (program : GeneratedProgram P.args) :
    GeneratedProgram Q.args :=
  lower (mapGraph h program.source)

structure Sentence (P : EntrySignature) where
  lhs : GeneratedProgram P.args
  rhs : GeneratedProgram P.args

def Sentence.map (h : P ⟶ Q) (e : Sentence P) : Sentence Q :=
  ⟨e.lhs.map h, e.rhs.map h⟩

def lowerEquation (e : Equation P) : Sentence P :=
  ⟨GeneratedProgram.lower e.lhs, GeneratedProgram.lower e.rhs⟩

/-- The actual root runs with an empty SSA environment, captured typed
scalar inputs, and the given initialized rank-one buffer. The entry
edge itself supplies the entry occurrence to the header. -/
def GeneratedProgram.Returns (program : GeneratedProgram P.args) (model : EntryModel P)
    (initial : Buffer model.cells) (result : Word × Buffer model.cells) : Prop :=
  ∃ budget, MemRef.runProgram (program.cfg model.cells) program.source model.input budget initial = some result

/-- A finite observation contains the returned word and the entire final
buffer. Exhausting one allowance is compatible with a finite return. -/
noncomputable def GeneratedProgram.observe (program : GeneratedProgram P.args) (model : EntryModel P)
    (initial : Buffer model.cells) : Part (Word × Buffer model.cells) where
  Dom := ∃ result, program.Returns model initial result
  get found := Classical.choose found

/-- At a model's typed valuation, compare every initialized buffer. -/
def Sentence.Holds (e : Sentence P) (model : EntryModel P) : Prop :=
  ∀ initial : Buffer model.cells, e.lhs.observe model initial = e.rhs.observe model initial

def room (P : EntrySignature) : Room.{0, 0, 0} where
  Sen := Sentence P
  Mod := (Institution.room P).Mod
  Sat model e := e.Holds model.as

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.MemRefRoom
