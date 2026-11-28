module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Defs

/-! # Checked inner reconvergence before the outer merge -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared

open SeaOfNodes.Diamond (Model ValueSort)
open Join (Block)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}

/-- The checked block order includes the common inner suffix once. The
outer false route stays disjoint and reaches the original common merge. -/
structure Program (src : Source Op regs out size) (entry : Fin size) extends Control src entry where
  meet : Fin size
  innerTrue : Chain.Segment src meet onInnerTrue
  innerFalse : Chain.Segment src meet onInnerFalse
  suffix : Chain.Segment src join meet
  outerFalse : Chain.Segment src join onOuterFalse
  nonempty : suffix.blocks ≠ []
  distinct : ([entry, header, inner] ++ innerTrue.blocks ++ innerFalse.blocks ++ suffix.blocks ++
    outerFalse.blocks ++ [join, latch]).Nodup
  covers : ([entry, header, inner] ++ innerTrue.blocks ++ innerFalse.blocks ++ suffix.blocks ++
    outerFalse.blocks ++ [join, latch]).length = size

/-- Check disjointness and coverage of the factored routes. -/
def Program.admit (control : Control src entry) (meet : Fin size)
    (innerTrue : Chain.Segment src meet control.onInnerTrue)
    (innerFalse : Chain.Segment src meet control.onInnerFalse)
    (suffix : Chain.Segment src control.join meet)
    (outerFalse : Chain.Segment src control.join control.onOuterFalse) : Option (Program src entry) :=
  let order := [entry, control.header, control.inner] ++ innerTrue.blocks ++ innerFalse.blocks ++
    suffix.blocks ++ outerFalse.blocks ++ [control.join, control.latch]
  if shape : suffix.blocks ≠ [] ∧ order.Nodup ∧ order.length = size then
    some ⟨control, meet, innerTrue, innerFalse, suffix, outerFalse, shape.1, shape.2.1, shape.2.2⟩
  else none

/-- Find the first common site along the true path, cut both paths there,
and validate the factored shape against the entire ordered source table. -/
def check (src : Source Op regs out size) (entry : Fin size) : Option (Program src entry) := do
  let routes ← Nested.findRoutes src entry
  let some meet := routes.innerTrue.blocks.find? routes.innerFalse.blocks.contains | none
  let yes ← routes.innerTrue.cutAt meet
  let no ← routes.innerFalse.cutAt meet
  Program.admit routes.toControl meet yes.1 no.1 yes.2 routes.outerFalse

variable (p : Program src entry)

def Program.blockOrder : List (Fin size) :=
  [entry, p.header, p.inner] ++ p.innerTrue.blocks ++ p.innerFalse.blocks ++ p.suffix.blocks ++
    p.outerFalse.blocks ++ [p.join, p.latch]

/-- The predecessor and outgoing slot at the inner reconvergence. The
final jump of a nonempty prefix occupies slot zero. -/
def Program.innerEdgeOccurrence (taken : Bool) : Fin size × Fin 2 :=
  match taken with
  | true => (p.innerTrue.predecessor p.inner, 0)
  | false => (p.innerFalse.predecessor p.inner, bif p.innerFalse.blocks.isEmpty then 1 else 0)

def Program.prefixTarget : Occurrence → Fin size
  | .innerTrue | .innerFalse => p.meet
  | .outerFalse => p.join

def Program.prefixQuads (occurrence : Occurrence) : Block Op regs :=
  (src p.header).body ++ match occurrence with
  | .innerTrue => (src p.inner).body ++ p.innerTrue.quads
  | .innerFalse => (src p.inner).body ++ p.innerFalse.quads
  | .outerFalse => p.outerFalse.quads

/-- Each prefix supplies its independently compiled latest definitions. -/
def Program.prefixTransfer (occurrence : Occurrence) :=
  CFG.compileBlock (p.prefixQuads occurrence) (initial regs)

/-- The shared segment takes a single full typed bank at the reconvergence. -/
def Program.suffixTransfer :=
  CFG.compileBlock p.suffix.quads (initial regs)

def Program.prefixBank (m : Model.{u, v, w} Op) (old : Bank (regs := regs) m)
    (occurrence : Occurrence) : Bank (regs := regs) m :=
  let compiled := p.prefixTransfer occurrence
  compiled.outgoing.read old (compiled.flow.eval m old PUnit.unit)

def Program.suffixBank (m : Model.{u, v, w} Op) (incoming : Bank (regs := regs) m) : Bank (regs := regs) m :=
  let compiled := p.suffixTransfer
  compiled.outgoing.read incoming (compiled.flow.eval m incoming PUnit.unit)

def Program.mergeBank (m : Model.{u, v, w} Op) (old : Bank (regs := regs) m)
    (occurrence : Occurrence) : Bank (regs := regs) m :=
  let incoming := p.prefixBank m old occurrence
  match occurrence with
  | .innerTrue | .innerFalse => p.suffixBank m incoming
  | .outerFalse => incoming

def Program.prefixVisits : Occurrence → Nat
  | .innerTrue => p.innerTrue.blocks.length + 2
  | .innerFalse => p.innerFalse.blocks.length + 2
  | .outerFalse => p.outerFalse.blocks.length + 1

def Program.mergeVisits (occurrence : Occurrence) : Nat :=
  p.prefixVisits occurrence + match occurrence with
    | .innerTrue | .innerFalse => p.suffix.blocks.length
    | .outerFalse => 0

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared
