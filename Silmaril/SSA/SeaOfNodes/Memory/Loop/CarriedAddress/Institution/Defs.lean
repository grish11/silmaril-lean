module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Petri.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.MemRef.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Institution.RuntimeObservation.Defs

/-! Finite observations and equations for the single-address-Phi loop. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution

open CategoryTheory Silmaril.Logic.Institution
open RVSDG.NestedTheta.Petri (Finishes)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q : EntrySignature} {cells : Nat}

/-- Extend a typed entry map under the address bound by the Phi. -/
def liftAddress (h : P ⟶ Q) : (⟨.address :: P.args⟩ : EntrySignature) ⟶ ⟨.address :: Q.args⟩ :=
  ⟨fun
    | .head => .head
    | .tail p => .tail (EntrySignature.Hom.port h p)⟩

/-- Rename the invariant ports and both Phi operands. The arrival
occurrence still chooses its own column. -/
def mapGraph (h : P ⟶ Q) (graph : Graph P.args) : Graph Q.args where
  activation := Loop.Institution.mapGraph (liftAddress h) graph.activation
  entryAddress := EntrySignature.Hom.port h graph.entryAddress
  backedgeAddress := EntrySignature.Hom.port h graph.backedgeAddress

structure Equation (P : EntrySignature) where
  lhs : Graph P.args
  rhs : Graph P.args

def Equation.map (h : P ⟶ Q) (e : Equation P) : Equation Q :=
  ⟨mapGraph h e.lhs, mapGraph h e.rhs⟩

/-- At a fixed typed valuation and cell count, observe the returned
word and entire final heap for each initialized heap. -/
abbrev Observation (cells : Nat) := Heap cells → Word → Heap cells → Prop

def Observation.NoReturn {cells : Nat} (returns : Observation cells) (initial : Heap cells) : Prop :=
  ∀ word final, ¬ returns initial word final

def nativeReturns (graph : Graph P.args) (model : EntryModel P) : Observation model.cells :=
  fun initial word final => ∃ budget, graph.evalWithin model.input budget .entry initial = some (word, final)

def petriReturns (graph : Graph P.args) (model : EntryModel P) : Observation model.cells :=
  fun initial word final => Finishes (thetaRuntime model.cells) (Petri.lower graph)
    (Petri.encodeArrival .entry initial model.input) (encodeResult word final)

def memrefReturns (graph : Graph P.args) (model : EntryModel P) : Observation model.cells :=
  fun initial word final => ∃ budget, MemRef.run graph model.input budget ⟨initial⟩ = some (word, ⟨final⟩)

/-- The existing nested RVSDG observer at the emitted program and encoded entry.
The canonical runtime model uses the native model's initialized cell count. -/
noncomputable def runtimeObserve (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    Part (RVSDG.Tuple (WireVal model.cells) (RVSDG.OrderedRuntime.Structured.Threaded wordPorts)) :=
  RVSDG.NestedTheta.Institution.RuntimeObservation.observe (P := ⟨ThetaOpcode⟩)
    (thetaRuntime model.cells) (Petri.lower graph) (Petri.encodeArrival .entry initial model.input)

/-- Compare the sets of complete finite observations. If both sides have
no finite return for a heap, both sets are empty there. -/
def Equation.HoldsWith (e : Equation P) (observe : Graph P.args → Observation cells) : Prop :=
  ∀ initial word final, observe e.lhs initial word final ↔ observe e.rhs initial word final

def Equation.Holds (e : Equation P) (model : EntryModel P) : Prop :=
  e.HoldsWith (nativeReturns · model)

def petriHolds (e : Equation P) (model : EntryModel P) : Prop :=
  e.HoldsWith (petriReturns · model)

def memrefHolds (e : Equation P) (model : EntryModel P) : Prop :=
  e.HoldsWith (memrefReturns · model)

def room (P : EntrySignature) : Room.{0, 0, 0} where
  Sen := Equation P
  Mod := Cat.of (Discrete (EntryModel P))
  Sat model e := e.Holds model.as

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution
