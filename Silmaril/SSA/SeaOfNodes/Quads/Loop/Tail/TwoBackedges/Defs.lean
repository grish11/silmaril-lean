module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Defs

/-! A pure quad loop whose two feedback blocks enter the same header. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges

open Diamond (Model Signature ValueSort dataPorts sortValue)
open RVSDG (Port)
open Blocks (Bank)
open Join (Block)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}

/-- The arriving edge identifies the complete register column it supplies. -/
inductive Incoming where
  | entry
  | feedback (side : Bool)
  deriving DecidableEq, Repr

/-- After the header's pure assignments, the continuation test either
returns or enters a dispatcher. Each dispatch arm jumps back independently. -/
structure Program (Op : Signature.{u, v} Data) (regs : List (ValueSort Data)) (out : ValueSort Data) where
  preheader : Block Op regs
  header : Block Op regs
  again : Port (dataPorts regs) (.value .predicate)
  select : Port (dataPorts regs) (.value .predicate)
  result : Port (dataPorts regs) (.value out)
  feedback : Bool → Block Op regs

def feedbackBlock (side : Bool) : Fin 5 := if side then 3 else 4

/-- Blocks 0, 1 and 2 are entry, header and dispatch. The two feedback
blocks have separate jumps to block 1. -/
def Program.source (p : Program Op regs out) : Tail.Source Op regs out 5 :=
  fun index =>
    if index = 0 then ⟨p.preheader, .transfer (.jump 1)⟩
    else if index = 1 then ⟨p.header, .branch p.again (.jump 2) (.ret p.result)⟩
    else if index = 2 then ⟨[], .branch p.select (.jump (feedbackBlock true)) (.jump (feedbackBlock false))⟩
    else ⟨p.feedback (index == feedbackBlock true), .transfer (.jump 1)⟩

/-- Group one native header visit with the dispatch and selected feedback
block when continuing. The feedback label retains the arriving occurrence. -/
def Program.step (p : Program Op regs out) (m : Model.{u, v, w} Op) (old : Bank (regs := regs) m) :
    sortValue m.value out ⊕ (Bool × Bank (regs := regs) m) :=
  let current := p.header.eval m old
  if (current.get p.again).down then
    let side := (current.get p.select).down
    .inr (side, (p.feedback side).eval m current)
  else .inl (current.get p.result)

/-- Finite header arrivals include prefixes of executions that never return. -/
inductive Program.Arrives (p : Program Op regs out) (m : Model.{u, v, w} Op)
    (input : Bank (regs := regs) m) : Incoming → Nat → Bank (regs := regs) m → Prop where
  | entry : Arrives p m input .entry 0 (p.preheader.eval m input)
  | feedback {via count old side next} (prior : Arrives p m input via count old)
      (taken : p.step m old = .inr (side, next)) : Arrives p m input (.feedback side) (count + 1) next

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges
