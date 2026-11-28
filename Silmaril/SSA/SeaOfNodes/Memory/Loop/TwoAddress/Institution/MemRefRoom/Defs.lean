module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Reindex.Defs

/-! Generated MemRef equations and termination over initialized buffers. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.MemRefRoom

open CategoryTheory Silmaril.Logic.Institution
open RVSDG.NestedTheta.Institution
open Silmaril.MLIR.MemRef (Buffer)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q : EntrySignature} {args : List ValueSort}

/-- Each sentence retains its source and actual CFG at every cell count.
The source determines how to re-emit the program along a typed port map. -/
structure GeneratedProgram (args : List ValueSort) where
  source : Graph args
  cfg : (cells : Nat) → MemRef.Program cells args
  generated : cfg = fun cells => MemRef.lower cells source

def GeneratedProgram.lower (graph : Graph args) : GeneratedProgram args :=
  ⟨graph, fun cells => MemRef.lower cells graph, rfl⟩

/-- Observe the stored CFG at its emitted entry with an initialized buffer
and the model's typed input tuple. -/
def GeneratedProgram.Returns (program : GeneratedProgram P.args) (model : EntryModel P)
    (initial : Buffer model.cells) (result : Word × Buffer model.cells) : Prop :=
  ∃ fuel, MemRef.runProgram (program.cfg model.cells) model.input fuel initial = some result

inductive Sentence (P : EntrySignature) where
  | equation (lhs rhs : GeneratedProgram P.args)
  | terminates (program : GeneratedProgram P.args)

def Sentence.lower : Institution.Sentence P → Sentence P
  | .equation lhs rhs => .equation (.lower lhs) (.lower rhs)
  | .terminates graph => .terminates (.lower graph)

def Sentence.source : Sentence P → Institution.Sentence P
  | .equation lhs rhs => .equation lhs.source rhs.source
  | .terminates program => .terminates program.source

/-- Re-emit after renaming the captured ports. -/
def Sentence.map (h : P ⟶ Q) (s : Sentence P) : Sentence Q :=
  lower (s.source.map h)

/-- At the model's valuation, equation truth compares complete finite
returns and termination requires a finite return at every buffer. -/
def Sentence.Holds (s : Sentence P) (model : EntryModel P) : Prop :=
  match s with
  | .equation lhs rhs =>
    ∀ initial word final, lhs.Returns model initial (word, final) ↔ rhs.Returns model initial (word, final)
  | .terminates program => ∀ initial, ∃ word final, program.Returns model initial (word, final)

/-- The existing numbered-runtime sentence for the retained source. -/
def Sentence.numbered (s : Sentence P) : RuntimeObservation.Sentence target :=
  translate s.source

def room (P : EntrySignature) : Room.{0, 0, 0} where
  Sen := Sentence P
  Mod := (Institution.room P).Mod
  Sat m s := s.Holds m.as

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.MemRefRoom
