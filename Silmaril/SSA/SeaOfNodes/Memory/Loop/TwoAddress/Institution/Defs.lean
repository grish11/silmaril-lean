module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.MemRef.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Petri.Defs

/-! Two-address observations at a typed entry valuation and initialized heap. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution

open RVSDG (Tuple)
open RVSDG.NestedTheta.Institution
open RVSDG.NestedTheta.Petri (Finishes)
open RVSDG.OrderedRuntime.Structured (Threaded)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open CarriedAddress.Institution (Observation)

variable {P : EntrySignature} {cells : Nat}

/-- Partial equality compares complete finite returns. Termination
requires a finite return at every initial heap. -/
inductive Sentence (P : EntrySignature) where
  | equation (lhs rhs : Graph P.args)
  | terminates (graph : Graph P.args)

def Sentence.HoldsWith (s : Sentence P) (observe : Graph P.args → Observation cells) : Prop :=
  match s with
  | .equation lhs rhs => ∀ initial word final, observe lhs initial word final ↔ observe rhs initial word final
  | .terminates graph => ∀ initial, ∃ word final, observe graph initial word final

def nativeReturns (graph : Graph P.args) (model : EntryModel P) : Observation model.cells :=
  graph.Returns model.input

def petriReturns (graph : Graph P.args) (model : EntryModel P) : Observation model.cells :=
  fun initial word final => Finishes (thetaRuntime model.cells) (Petri.lower graph)
    (encodeInput initial model.input) (encodeResult word final)

def memrefReturns (graph : Graph P.args) (model : EntryModel P) : Observation model.cells :=
  fun initial word final => ∃ fuel, MemRef.runFuel graph model.input fuel ⟨initial⟩ = some (word, ⟨final⟩)

def Sentence.Holds (s : Sentence P) (model : EntryModel P) : Prop :=
  s.HoldsWith (nativeReturns · model)

/-- At the chosen cell count, quantify over all typed input tuples. -/
def Sentence.HoldsAt (s : Sentence P) (cells : Nat) : Prop :=
  ∀ input : Tuple (Val cells) P.args, s.Holds ⟨cells, input⟩

def Sentence.MemRefHolds (s : Sentence P) (cells : Nat) : Prop :=
  ∀ input : Tuple (Val cells) P.args, s.HoldsWith (memrefReturns · ⟨cells, input⟩)

def Sentence.PetriHolds (s : Sentence P) (cells : Nat) : Prop :=
  ∀ input : Tuple (Val cells) P.args, s.HoldsWith (petriReturns · ⟨cells, input⟩)

/-- Fix the existing ordered runtime opcode alphabet. The native entry
signature determines the typed boundary of each translated program. -/
abbrev target : RVSDG.Institution.Signature ValueSort PUnit := ⟨ThetaOpcode⟩

def lowerProgram (graph : Graph P.args) :
    RuntimeObservation.Program target (carrier P.args) (Threaded wordPorts) :=
  ⟨_, Petri.lower graph⟩

/-- The actual numbered θ programs are sentences in the existing room. -/
def translate : Sentence P → RuntimeObservation.Sentence target
  | .equation lhs rhs => .equation (lowerProgram lhs) (lowerProgram rhs)
  | .terminates graph => .terminates (lowerProgram graph)

noncomputable def runtimeObserve (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    Part (Tuple (WireVal model.cells) (Threaded wordPorts)) :=
  RuntimeObservation.observe (P := target) (thetaRuntime model.cells) (lowerProgram graph).graph
    (encodeInput initial model.input)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution
