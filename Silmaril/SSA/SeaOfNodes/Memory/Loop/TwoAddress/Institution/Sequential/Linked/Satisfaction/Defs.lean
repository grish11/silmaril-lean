module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.MemRef.Defs

/-! Typed linked programs and their sentences in the existing numbered runtime room. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction

open CategoryTheory
open RVSDG (Tuple)
open RVSDG.NestedTheta.Institution
open Silmaril.MLIR.MemRef (Buffer)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q : EntrySignature} {cells : Nat}

/-- The outer signature is the ambient capture bank. Each sequence
retains its own typed second-stage boundary and static wiring. -/
structure Program (P : EntrySignature) where
  next : EntrySignature
  first : Graph P.args
  second : Graph next.args
  wiring : Boundary.Wiring P.args next.args

/-- Re-emit the first loop at the new ambient boundary. The second loop
keeps its own entry signature and reads the reindexed capture wiring. -/
def Program.map (h : P ⟶ Q) (p : Program P) : Program Q :=
  ⟨p.next, mapGraph h p.first, p.second, p.wiring.map (EntrySignature.Hom.port h)⟩

def Program.emitNumbered (p : Program P) :
    RuntimeObservation.Program target (carrier P.args) (carrier [.word, .word]) :=
  ⟨_, Linked.lower p.first p.second p.wiring⟩

def Program.numberedChecked (p : Program P) :
    RVSDG.NestedTheta.ExplicitRuntime.EntryChecked
      (a := inputData P.args) (b := inputData [.word, .word]) p.emitNumbered.graph.toTerm :=
  Linked.checked p.first p.second p.wiring

def Program.emitMemRef (p : Program P) (cells : Nat) :=
  Linked.MemRef.lower cells p.first p.second

def Program.runMemRef (p : Program P) (model : EntryModel P) (fuel : Nat) (initial : Buffer model.cells) :
    Option (Linked.MemRef.Result model.cells) :=
  Linked.MemRef.runFuel p.first p.second p.wiring model.input fuel initial

def Program.equation (lhs rhs : Program P) : RuntimeObservation.Sentence target :=
  .equation lhs.emitNumbered rhs.emitNumbered

def Program.terminates (p : Program P) : RuntimeObservation.Sentence target :=
  .terminates p.emitNumbered

abbrev Returns (cells : Nat) := Heap cells → Result cells → Prop

/-- Compare partial results at every initialized heap of a fixed valuation. -/
def Agrees (lhs rhs : Returns cells) : Prop :=
  ∀ initial out, lhs initial out ↔ rhs initial out

def Terminates (returns : Returns cells) : Prop :=
  ∀ initial, ∃ out, returns initial out

def Program.nativeReturns (p : Program P) (model : EntryModel P) : Returns model.cells :=
  fun initial (word, nextWord, final) =>
    ∃ middle, Institution.nativeReturns p.first model initial word middle ∧
      Institution.nativeReturns p.second ⟨model.cells, p.wiring.select word model.input⟩ middle nextWord final

noncomputable def Program.sequentialObserve (p : Program P) (model : EntryModel P)
    (initial : Heap model.cells) : Part (Result model.cells) :=
  Sequential.numbered (RuntimeRoom.GeneratedProgram.lower p.first) (RuntimeRoom.GeneratedProgram.lower p.second)
    model (fun word => p.wiring.select word model.input) initial

noncomputable def Program.numberedObserve (p : Program P) (model : EntryModel P)
    (initial : Heap model.cells) : Part (Tuple (WireVal model.cells) (carrier [.word, .word])) :=
  RuntimeObservation.observe (P := target) (thetaRuntime model.cells) p.emitNumbered.graph
    (encodeInput initial model.input)

def Program.memrefReturns (p : Program P) (model : EntryModel P) : Returns model.cells :=
  fun initial (word, nextWord, final) =>
    ∃ fuel, p.runMemRef model fuel ⟨initial⟩ = some (word, nextWord, ⟨final⟩)

def Program.colouredReturns (p : Program P) (model : EntryModel P) : Returns model.cells :=
  fun initial out =>
    RVSDG.NestedTheta.Petri.Finishes (thetaRuntime model.cells) p.emitNumbered.graph
      (encodeInput initial model.input) (resultCodec model.cells out)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction
