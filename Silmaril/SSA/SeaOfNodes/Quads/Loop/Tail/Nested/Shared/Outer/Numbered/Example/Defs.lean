module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Example.Defs

/-! # Both outer routes use one two-block suffix -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Example

open Diamond.MLIR.CF.Example (add count input num regs result stride test)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.Diamond (dataPorts lastIndex)
open RVSDG.NestedTheta (Graph)
open Shared.Numbered.Example (FixturePort)
open Blocks (Bank)

abbrev original := Shared.MLIR.CF.Example.source

/-- Preserve the original fixture IDs and insert the common outer tail
10 → 11 before join 8. The exclusive inner suffix is still 5 → 6. -/
def source : Source Op regs num 12
  | 0 => ⟨(original 0).body, .transfer (.jump 1)⟩
  | 1 => ⟨(original 1).body, .branch test (.jump 2) (.jump 7)⟩
  | 2 => ⟨(original 2).body, .branch test (.jump 3) (.jump 4)⟩
  | 3 => ⟨(original 3).body, .transfer (.jump 5)⟩
  | 4 => ⟨(original 4).body, .transfer (.jump 5)⟩
  | 5 => ⟨(original 5).body, .transfer (.jump 6)⟩
  | 6 => ⟨(original 6).body, .transfer (.jump 10)⟩
  | 7 => ⟨(original 7).body, .transfer (.jump 10)⟩
  | 8 => ⟨(original 8).body, .transfer (.jump 9)⟩
  | 9 => ⟨(original 9).body, .branch test (.jump 1) (.ret result)⟩
  | 10 => ⟨[add result result stride], .transfer (.jump 11)⟩
  | _ => ⟨[add result result stride], .transfer (.jump 8)⟩

/-- The outer false path overlaps the inner true prefix before inner
reconvergence. Every site remains reachable across the three routes. -/
def crossesInnerPrefix : Source Op regs num 12 := fun id =>
  if id = 7 then {source id with terminator := .transfer (.jump 3)}
  else source id

def plan : Program source 0 := (Outer.check source 0).get (by rfl)

def headerStates : List (Bank (regs := regs) model) :=
  let first := (source 0).body.eval model input
  let second := nextBank plan model first
  [first, second, nextBank plan model second]

def trace : List (Occurrence × (Nat × Nat) × Nat) :=
  headerStates.map fun old =>
    let occurrence := plan.toControl.selected model old
    let edge := plan.outerEdgeOccurrence (occurrence != .outerFalse)
    (occurrence, (edge.1.val, edge.2.val), plan.mergeVisits occurrence)

def outerValues : List (Option Nat) :=
  headerStates.map fun old =>
    ((outerRegion plan).toGraph.run (Join.model model) 0 old).map fun bank => (bank.get result).toNat

def mergeValues : List (Option Nat) :=
  headerStates.map fun old =>
    ((mergeRegion plan).toGraph.run (Join.model model) 0 old).map fun bank => (bank.get result).toNat

/-- Read the actual tag, counter, and result slot at both feedback edges and exit. -/
def packets : List (Option (Nat × Nat × Nat)) :=
  headerStates.map fun old =>
    ((thetaBody plan).toGraph.run (Join.model model) 0 old).map fun
      | .cons tag bank => (tag.down.val, (bank.get count).toNat, (bank.get result).toNat)

/-- Inspect the actual body and reuse the inner-only layout inspector for
the embedded γ children. Count the outer continuation separately. -/
def layout : Option (Nat × Nat × List Nat × Nat) :=
  match lower plan with
  | .region nodes children _ =>
    let site := lastIndex (dataPorts regs) (source 0).body.producers
    if body : 0 < (nodes site).kind.arity then inspect (children site ⟨0, body⟩) else none
where
  inspect {args outs : List FixturePort} {sigs : List (List FixturePort)}
      (graph : Graph (Join.Opcode Op) args [] sigs outs) : Option (Nat × Nat × List Nat × Nat) :=
    match graph with
    | .region nodes _ _ => do
      let gamma ← (List.finRange sigs.length).find? fun i => (nodes i).kind.arity == 2
      let inner ← Shared.Numbered.Example.layout.outerLayout graph
      return (sigs.length - (gamma.val + 1), inner)

def sourceBudget (fuel : Nat) : Nat := sourceVisits plan model fuel input

def runSource (fuel : Nat) : Option Nat :=
  (source.runFrom model fuel 0 input).map BitVec.toNat

def runNumbered (fuel : Nat) : Option Nat :=
  ((lower plan).run (Join.model model) fuel input).map fun values => (values.get .head).toNat

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Example
