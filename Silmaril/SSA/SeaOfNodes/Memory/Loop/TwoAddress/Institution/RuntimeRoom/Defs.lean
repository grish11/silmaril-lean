module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Reindex.Defs

/-! Generated whole θ programs at canonical typed entry valuations. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom

open CategoryTheory Silmaril.Logic.Institution
open RVSDG (Tuple)
open RVSDG.NestedTheta.Institution
open RVSDG.OrderedRuntime.Structured (Threaded)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q : EntrySignature} {args : List ValueSort}

abbrev Program (args : List ValueSort) :=
  RuntimeObservation.Program target (carrier args) (Threaded wordPorts)

/-- Retain the source for re-emission along typed capture maps and the
actual numbered program for observation. -/
structure GeneratedProgram (args : List ValueSort) where
  source : Graph args
  program : Program args
  generated : program = lowerProgram (P := ⟨args⟩) source

def GeneratedProgram.lower (graph : Graph args) : GeneratedProgram args :=
  ⟨graph, lowerProgram (P := ⟨args⟩) graph, rfl⟩

def GeneratedProgram.map (h : P ⟶ Q) (program : GeneratedProgram P.args) :
    GeneratedProgram Q.args :=
  lower (mapGraph h program.source)

/-- Run the stored whole θ through the existing partial runtime observer.
The root entry carries the model's captures and every initialized cell. -/
noncomputable def GeneratedProgram.observe (program : GeneratedProgram P.args) (model : EntryModel P)
    (initial : Heap model.cells) : Part (Tuple (WireVal model.cells) (Threaded wordPorts)) :=
  RuntimeObservation.observe (P := target) (thetaRuntime model.cells) program.program.graph
    (encodeInput initial model.input)

inductive Sentence (P : EntrySignature) where
  | equation (lhs rhs : GeneratedProgram P.args)
  | terminates (program : GeneratedProgram P.args)

def Sentence.lower : Institution.Sentence P → Sentence P
  | .equation lhs rhs => .equation (.lower lhs) (.lower rhs)
  | .terminates graph => .terminates (.lower graph)

def Sentence.source : Sentence P → Institution.Sentence P
  | .equation lhs rhs => .equation lhs.source rhs.source
  | .terminates program => .terminates program.source

def Sentence.map (h : P ⟶ Q) (s : Sentence P) : Sentence Q :=
  lower (s.source.map h)

/-- Read the stored programs as a sentence of the existing numbered room. -/
def Sentence.numbered : Sentence P → RuntimeObservation.Sentence target
  | .equation lhs rhs => .equation lhs.program rhs.program
  | .terminates program => .terminates program.program

/-- Compare complete partial results or require a finite result for every
initialized heap at the valuation supplied by the observer. -/
def Sentence.HoldsWith (s : Sentence P) {cells : Nat}
    (observe : GeneratedProgram P.args → Heap cells → Part (Tuple (WireVal cells) (Threaded wordPorts))) : Prop :=
  match s with
  | .equation lhs rhs => ∀ initial, observe lhs initial = observe rhs initial
  | .terminates program => ∀ initial, (observe program initial).Dom

def Sentence.Holds (s : Sentence P) (model : EntryModel P) : Prop :=
  s.HoldsWith (GeneratedProgram.observe · model)

def room (P : EntrySignature) : Room.{0, 0, 0} where
  Sen := Sentence P
  Mod := (Institution.room P).Mod
  Sat m s := s.Holds m.as

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom
