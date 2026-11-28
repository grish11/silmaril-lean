module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeEntry.Thms

/-! A room for emitted single-address-Phi programs at validated runtime entries. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeRoom

open CategoryTheory Silmaril.Logic.Institution
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q : EntrySignature} {args : List ValueSort}

/-- An actual emitted program with the source needed to re-emit it at
renamed typed ports. -/
structure GeneratedProgram (args : List ValueSort) where
  source : Graph args
  program : RuntimeEntry.Program args
  generated : program = RuntimeEntry.lowerProgram source

def GeneratedProgram.lower (graph : Graph args) : GeneratedProgram args :=
  ⟨graph, RuntimeEntry.lowerProgram graph, rfl⟩

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

/-- A model fixes one typed valuation and cell count. Every initialized
heap at that model gives an admissible runtime entry. -/
def modelEntry (model : EntryModel P) (heap : Heap model.cells) :
    {raw : RuntimeEntry.RawEntry P.args model.cells // RuntimeEntry.Admissible raw} :=
  ⟨RuntimeEntry.Entry.encode ⟨model.input, heap⟩, RuntimeEntry.admissible_encode _⟩

/-- Exact equality of complete partial word-and-heap observations over all
initialized heaps at the chosen valuation. -/
def Sentence.Holds (e : Sentence P) (model : EntryModel P) : Prop :=
  ∀ heap, RuntimeEntry.observeProgram e.lhs.program (modelEntry model heap).val =
    RuntimeEntry.observeProgram e.rhs.program (modelEntry model heap).val

def room (P : EntrySignature) : Room.{0, 0, 0} where
  Sen := Sentence P
  Mod := (Institution.room P).Mod
  Sat model e := e.Holds model.as

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeRoom
