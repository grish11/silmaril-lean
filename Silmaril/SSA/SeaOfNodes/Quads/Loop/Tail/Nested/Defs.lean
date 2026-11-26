module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Segment.Defs

/-! # A checked nested split with one common three-occurrence merge -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested

open SeaOfNodes.Diamond (Model ValueSort dataPorts)
open RVSDG (Port)
open Join (Block)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}

/-- The outer true edge goes to the inner split. List incoming occurrences
in source traversal order: inner true, inner false, then outer false. -/
inductive Occurrence
  | innerTrue
  | innerFalse
  | outerFalse
  deriving DecidableEq, Repr

/-- The original split and loop terminators, independent of arm overlap. -/
structure Control (src : Source Op regs out size) (entry : Fin size) where
  header : Fin size
  inner : Fin size
  onInnerTrue : Fin size
  onInnerFalse : Fin size
  onOuterFalse : Fin size
  join : Fin size
  latch : Fin size
  outerTest : Port (dataPorts regs) (.value .predicate)
  innerTest : Port (dataPorts regs) (.value .predicate)
  again : Port (dataPorts regs) (.value .predicate)
  result : Port (dataPorts regs) (.value out)
  entryEdge : (src entry).terminator = .transfer (.jump header)
  outerEdge : (src header).terminator = .branch outerTest (.jump inner) (.jump onOuterFalse)
  innerEdge : (src inner).terminator = .branch innerTest (.jump onInnerTrue) (.jump onInnerFalse)
  joinEdge : (src join).terminator = .transfer (.jump latch)
  latchEdge : (src latch).terminator = .branch again (.jump header) (.ret result)

/-- The three paths found in the original table, before checking coverage. -/
structure Routes (src : Source Op regs out size) (entry : Fin size) extends Control src entry where
  innerTrue : Chain.Segment src join onInnerTrue
  innerFalse : Chain.Segment src join onInnerFalse
  outerFalse : Chain.Segment src join onOuterFalse

/-- Discover the merge from the outer false route and follow only checked
jumps on each route. The caller must still validate overlap and coverage. -/
def findRoutes (src : Source Op regs out size) (entry : Fin size) : Option (Routes src entry) :=
  match entryEdge : (src entry).terminator with
  | .transfer (.jump header) =>
    match outerEdge : (src header).terminator with
    | .branch outerTest (.jump inner) (.jump onOuterFalse) =>
      match innerEdge : (src inner).terminator with
      | .branch innerTest (.jump onInnerTrue) (.jump onInnerFalse) => do
        let outerRoute ← Chain.findPath src header size onOuterFalse
        let some join := outerRoute.beforeLatch | none
        let outerFalse ← outerRoute.segmentTo join
        let trueRoute ← Chain.findPath src header size onInnerTrue
        let falseRoute ← Chain.findPath src header size onInnerFalse
        let innerTrue ← trueRoute.segmentTo join
        let innerFalse ← falseRoute.segmentTo join
        match joinEdge : (src join).terminator with
        | .transfer (.jump latch) =>
          match latchEdge : (src latch).terminator with
          | .branch again (.jump target) (.ret result) =>
            if same : target = header then
              some ⟨⟨header, inner, onInnerTrue, onInnerFalse, onOuterFalse, join, latch, outerTest,
                innerTest, again, result, entryEdge, outerEdge, innerEdge, joinEdge, same ▸ latchEdge⟩,
                innerTrue, innerFalse, outerFalse⟩
            else none
          | _ => none
        | _ => none
      | _ => none
    | _ => none
  | _ => none

/-- The checked shape admits disjoint linear arms. Direct edges to the
merge have no arm blocks, and the two inner transfers may both be direct. -/
structure Program (src : Source Op regs out size) (entry : Fin size) extends Routes src entry where
  distinct : ([entry, header, inner] ++ innerTrue.blocks ++ innerFalse.blocks ++
    outerFalse.blocks ++ [join, latch]).Nodup
  covers : ([entry, header, inner] ++ innerTrue.blocks ++ innerFalse.blocks ++
    outerFalse.blocks ++ [join, latch]).length = size

def check (src : Source Op regs out size) (entry : Fin size) : Option (Program src entry) := do
  let p ← findRoutes src entry
  let order := [entry, p.header, p.inner] ++ p.innerTrue.blocks ++ p.innerFalse.blocks ++
    p.outerFalse.blocks ++ [p.join, p.latch]
  if shape : order.Nodup ∧ order.length = size then some ⟨p, shape.1, shape.2⟩ else none

/-- Both decisions use their own post-block bank. -/
def Control.selected {src : Source Op regs out size} {entry : Fin size}
    (p : Control src entry) (m : Model.{u, v, w} Op) (old : Bank (regs := regs) m) : Occurrence :=
  let outer := (src p.header).body.eval m old
  if (outer.get p.outerTest).down then
    let inner := (src p.inner).body.eval m outer
    if (inner.get p.innerTest).down then .innerTrue else .innerFalse
  else .outerFalse

variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)

def Program.armStart : Occurrence → Fin size
  | .innerTrue => p.onInnerTrue
  | .innerFalse => p.onInnerFalse
  | .outerFalse => p.onOuterFalse

def Program.arm (occurrence : Occurrence) : Chain.Segment src p.join (p.armStart occurrence) :=
  match occurrence with
  | .innerTrue => p.innerTrue
  | .innerFalse => p.innerFalse
  | .outerFalse => p.outerFalse

def Program.splitSite : Occurrence → Fin size
  | .innerTrue | .innerFalse => p.inner
  | .outerFalse => p.header

/-- Recover the original predecessor while retaining the occurrence that
identifies the route. A direct edge is owned by its split block. -/
def Program.predecessor (occurrence : Occurrence) : Fin size :=
  (p.arm occurrence).predecessor (p.splitSite occurrence)

/-- The original predecessor and its outgoing slot. A jump or true branch
uses slot zero. A false branch uses slot one when it directly enters the merge. -/
def Program.incomingEdge (occurrence : Occurrence) : Fin size × Fin 2 :=
  (p.predecessor occurrence,
    bif (p.arm occurrence).blocks.isEmpty then
      match occurrence with
      | .innerTrue => 0
      | .innerFalse | .outerFalse => 1
    else 0)

/-- Collect exactly the executed source writes before this merge input.
The join's own writes are outside all three incoming scopes. -/
def Program.pathQuads (occurrence : Occurrence) : Block Op regs :=
  (src p.header).body ++
    match occurrence with
    | .innerTrue | .innerFalse => (src p.inner).body ++ (p.arm occurrence).quads
    | .outerFalse => (p.arm occurrence).quads

def Program.incomingTransfer (occurrence : Occurrence) :=
  CFG.compileBlock (p.pathQuads occurrence) (initial regs)

/-- Read all Φ arguments from the same occurrence's final version map. -/
def Program.mergeBank (m : Model.{u, v, w} Op) (old : Bank (regs := regs) m)
    (occurrence : Occurrence) : Bank (regs := regs) m :=
  let compiled := p.incomingTransfer occurrence
  compiled.outgoing.read old (compiled.flow.eval m old PUnit.unit)

def Program.selected (m : Model.{u, v, w} Op) (old : Bank (regs := regs) m) : Occurrence :=
  p.toControl.selected m old

/-- Count source visits from the header up to, but excluding, the merge. -/
def Program.mergeVisits : Occurrence → Nat
  | .innerTrue => p.innerTrue.blocks.length + 2
  | .innerFalse => p.innerFalse.blocks.length + 2
  | .outerFalse => p.outerFalse.blocks.length + 1

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested
