module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Prefix.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Segment.Incoming.Defs

/-! # Opt-in outer reconvergence before the final join -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer

open SeaOfNodes.Diamond (Model ValueSort)
open Join (Block)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}

/-- A factorization of both ordered routes at their first shared block. -/
structure CommonTail {target leftStart rightStart : Fin size}
    (left : Chain.Segment src target leftStart) (right : Chain.Segment src target rightStart) where
  meet : Fin size
  leftPrefix : Chain.Segment src meet leftStart
  rightPrefix : Chain.Segment src meet rightStart
  suffix : Chain.Segment src target meet
  nonempty : suffix.blocks ≠ []
  leftOrder : left.blocks = leftPrefix.blocks ++ suffix.blocks
  rightOrder : right.blocks = rightPrefix.blocks ++ suffix.blocks

/-- The independently checked prefixes must account for both original
routes in order with one and the same nonempty suffix. -/
def commonTail {target leftStart rightStart : Fin size}
    (left : Chain.Segment src target leftStart) (right : Chain.Segment src target rightStart) :
    Option (CommonTail left right) := do
  let some meet := left.blocks.find? right.blocks.contains | none
  let yes ← left.cutAt meet
  let no ← right.cutAt meet
  if same : yes.2.blocks ≠ [] ∧ left.blocks = yes.1.blocks ++ yes.2.blocks ∧
      right.blocks = no.1.blocks ++ yes.2.blocks then
    some ⟨meet, yes.1, no.1, yes.2, same.1, same.2.1, same.2.2⟩
  else none

/-- A separate opt-in profile with nonempty inner-only and outer shared
tails. The checked order counts each source block exactly once. -/
structure Program (src : Source Op regs out size) (entry : Fin size) extends Prefix.Routes src entry where
  outerSuffix : Chain.Segment src join stop
  nonempty : suffix.blocks ≠ []
  outerNonempty : outerSuffix.blocks ≠ []
  distinct : ([entry, header, inner] ++ innerTrue.blocks ++ innerFalse.blocks ++ suffix.blocks ++
    outerFalse.blocks ++ outerSuffix.blocks ++ [join, latch]).Nodup
  covers : ([entry, header, inner] ++ innerTrue.blocks ++ innerFalse.blocks ++ suffix.blocks ++
    outerFalse.blocks ++ outerSuffix.blocks ++ [join, latch]).length = size

def Program.admit (routes : Prefix.Routes src entry)
    (outerSuffix : Chain.Segment src routes.join routes.stop)
    (outerNonempty : outerSuffix.blocks ≠ []) : Option (Program src entry) :=
  let order := [entry, routes.header, routes.inner] ++ routes.innerTrue.blocks ++ routes.innerFalse.blocks ++
    routes.suffix.blocks ++ routes.outerFalse.blocks ++ outerSuffix.blocks ++ [routes.join, routes.latch]
  if shape : routes.suffix.blocks ≠ [] ∧ order.Nodup ∧ order.length = size then
    some ⟨routes, outerSuffix, shape.1, outerNonempty, shape.2.1, shape.2.2⟩
  else none

/-- Cut both independently checked routes at the first common block and
certify the complete partition before admitting the program. -/
def check (src : Source Op regs out size) (entry : Fin size) : Option (Program src entry) := do
  let routes ← Nested.findRoutes src entry
  let inner ← commonTail routes.innerTrue routes.innerFalse
  let outer ← commonTail inner.suffix routes.outerFalse
  Program.admit ⟨routes.toControl, inner.meet, outer.meet, inner.leftPrefix, inner.rightPrefix,
    outer.leftPrefix, outer.rightPrefix⟩ outer.suffix outer.nonempty

variable (p : Program src entry)

def Program.blockOrder : List (Fin size) :=
  [entry, p.header, p.inner] ++ p.innerTrue.blocks ++ p.innerFalse.blocks ++ p.suffix.blocks ++
    p.outerFalse.blocks ++ p.outerSuffix.blocks ++ [p.join, p.latch]

abbrev Program.innerEdgeOccurrence (taken : Bool) := p.toRoutes.innerEdgeOccurrence taken

/-- The outer true predecessor finishes the exclusive inner suffix.
The outer false route can enter directly from the header's false slot. -/
def Program.outerEdgeOccurrence (taken : Bool) : Fin size × Fin 2 :=
  match taken with
  | true => (p.suffix.predecessor p.inner, 0)
  | false => (p.outerFalse.predecessor p.header, bif p.outerFalse.blocks.isEmpty then 1 else 0)

/-- Bank at the original outer predecessor, before its final producer
table. On the inner routes the exclusive suffix is nonempty. -/
def Program.outerPredecessorBank (m : Model.{u, v, w} Op) (old : Bank (regs := regs) m)
    (occurrence : Occurrence) : Bank (regs := regs) m :=
  let header := (src p.header).body.eval m old
  match occurrence with
  | .outerFalse => p.outerFalse.predecessorBank m old header
  | .innerTrue | .innerFalse =>
    p.suffix.predecessorBank m header (p.toRoutes.prefixBank m old occurrence)

/-- The common outer tail takes the selected outer γ bank as its input. -/
def Program.outerSuffixTransfer :=
  CFG.compileBlock p.outerSuffix.quads (initial regs)

abbrev Program.outerBank (m : Model.{u, v, w} Op) (old : Bank (regs := regs) m) (occurrence : Occurrence) :=
  p.toRoutes.outerBank m old occurrence

def Program.outerSuffixBank (m : Model.{u, v, w} Op) (incoming : Bank (regs := regs) m) :
    Bank (regs := regs) m :=
  let compiled := p.outerSuffixTransfer
  compiled.outgoing.read incoming (compiled.flow.eval m incoming PUnit.unit)

def Program.mergeBank (m : Model.{u, v, w} Op) (old : Bank (regs := regs) m)
    (occurrence : Occurrence) : Bank (regs := regs) m :=
  p.outerSuffixBank m (p.outerBank m old occurrence)

abbrev Program.outerVisits (occurrence : Occurrence) := p.toRoutes.outerVisits occurrence

def Program.mergeVisits (occurrence : Occurrence) : Nat :=
  p.outerVisits occurrence + p.outerSuffix.blocks.length

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer
