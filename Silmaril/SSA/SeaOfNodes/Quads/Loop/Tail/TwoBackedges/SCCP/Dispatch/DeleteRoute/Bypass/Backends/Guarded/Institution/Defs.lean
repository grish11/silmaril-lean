module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.EntryGuard.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Observation.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Defs
public import Silmaril.Logic.Institution.Syntactic.Defs

/-! Native partial words and generated observers at a fixed typed entry boundary. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution

open CategoryTheory Silmaril.Logic.Institution
open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Width)
open Blocks (Bank)
open RVSDG (Tuple)
open RVSDG.NestedTheta.Petri (Finishes)

abbrev Entry (regs : List (ValueSort Width)) := Bank (regs := regs) model
abbrev EntryFacts (regs : List (ValueSort Width)) := Tuple (Fact Word) (dataPorts regs)

variable {regs : List (ValueSort Width)} {result : Width}
variable [BankDecidableEq Word (dataPorts regs)]

/-- A native program with its facts and evidence of actual singleton admission. -/
structure Admitted (regs : List (ValueSort Width)) (result : Width)
    [BankDecidableEq Word (dataPorts regs)] where
  source : Program Op regs (.data result)
  facts : EntryFacts regs
  checked : Checked model source facts
  admitted : Worklist.admit model source facts = .ok checked

/-- Run the existing FIFO admission once, for both emitted targets. -/
def admit (source : Program Op regs (.data result)) (facts : EntryFacts regs) :
    Except Refusal (Admitted regs result) :=
  match h : Worklist.admit model source facts with
  | .ok checked => .ok ⟨source, facts, checked, h⟩
  | .error reason => .error reason

/-- Petri uses the same guarded numbered graph as the numbered evaluator. -/
structure Artifacts (regs : List (ValueSort Width)) (result : Width) where
  cf : Bypass.MLIR.CF.EntryGuard.Target regs result
  numbered : Bypass.Numbered.EntryGuard.Target regs result

def Admitted.emit (p : Admitted regs result) : Artifacts regs result :=
  ⟨Bypass.MLIR.CF.EntryGuard.lower p.checked, Bypass.Numbered.EntryGuard.lower p.checked⟩

/-- A native return is witnessed by a finite run from the original preheader. -/
def SourceReturns (source : Program Op regs (.data result)) (input : Entry regs)
    (word : Word result) : Prop :=
  ∃ fuel, source.source.runFrom model fuel 0 input = some word

noncomputable def Admitted.observe (p : Admitted regs result) (input : Entry regs) :
    Part (Word result) :=
  Total.sourcePart p.source input

inductive Backend where
  | cf
  | numbered
  | petri

/-- Each observer has its own witness for the exact word and target packet. -/
def Backend.Returns (backend : Backend) (artifacts : Artifacts regs result) (input : Entry regs)
    (word : Word result) : Prop :=
  match backend with
  | .cf => ∃ fuel, artifacts.cf.run evalOp fuel (encodeValues input) = some (.cons word .nil)
  | .numbered => artifacts.numbered.2.Returns (Join.model model) input (.cons word .nil)
  | .petri => Finishes (Join.model model) artifacts.numbered.2 input (.cons word .nil)

/-- Observe Petri independently by the existence of a finite completed trace. -/
noncomputable def Artifacts.petriPart (artifacts : Artifacts regs result) (input : Entry regs) :
    Part (Word result) :=
  ⟨∃ word, Backend.petri.Returns artifacts input word, fun h => Classical.choose h⟩

noncomputable def Backend.observe (backend : Backend) (artifacts : Artifacts regs result)
    (input : Entry regs) : Part (Word result) :=
  match backend with
  | .cf => Total.observeCF artifacts.cf input
  | .numbered => Total.observeNumbered artifacts.numbered.2 input
  | .petri => artifacts.petriPart input

/-- The two sentence forms share the same observer at a typed valuation. -/
inductive Sentence (P : Type) where
  | equation (lhs rhs : P)
  | terminates (program : P)

def Sentence.map {P Q : Type} (f : P → Q) : Sentence P → Sentence Q
  | .equation lhs rhs => .equation (f lhs) (f rhs)
  | .terminates program => .terminates (f program)

def Sentence.Holds {P : Type} (observe : P → Part (Word result)) : Sentence P → Prop
  | .equation lhs rhs => observe lhs = observe rhs
  | .terminates program => (observe program).Dom

/-- Models are typed entry valuations, with the primitive interpretation fixed. -/
def observationRoom {P : Type} (observe : P → Entry regs → Part (Word result)) : Room.{0, 0, 0} where
  Sen := Sentence P
  Mod := Cat.of (Discrete (Entry regs))
  Sat input sentence := sentence.Holds (fun p => observe p input.as)

noncomputable def sourceRoom (regs : List (ValueSort Width)) (result : Width)
    [BankDecidableEq Word (dataPorts regs)] : Room.{0, 0, 0} :=
  observationRoom (Admitted.observe (regs := regs) (result := result))

noncomputable def targetRoom (regs : List (ValueSort Width)) (result : Width) (backend : Backend) :
    Room.{0, 0, 0} :=
  observationRoom (fun (p : Artifacts regs result) input => backend.observe p input)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution
