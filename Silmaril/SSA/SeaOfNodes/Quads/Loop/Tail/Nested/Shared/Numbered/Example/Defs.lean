module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.Example.Defs

/-! # Inspect and run the actual θ for the existing two-block suffix fixture -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Example

open Diamond.MLIR.CF.Example (count input regs result)
open Shared.MLIR.CF.Example (plan source)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.Diamond (dataPorts lastIndex ValueSort)
open Silmaril.MLIR.Arith (Width)
open RVSDG.NestedTheta (Graph)
open Join (Opcode)
open Blocks (Bank)

abbrev FixturePort := RVSDG.PortType (ValueSort Width) PEmpty.{1}

def runNumbered (fuel : Nat) : Option Nat :=
  ((lower plan).run (Join.model model) fuel input).map (fun values => (values.get .head).toNat)

def sourceBudget (fuel : Nat) : Nat := sourceVisits plan model fuel input

def headerStates : List (Bank (regs := regs) model) :=
  let first := (source 0).body.eval model input
  let second := Shared.MLIR.CF.Example.nextBank first
  [first, second, Shared.MLIR.CF.Example.nextBank second]

def mergeValues : List (Option Nat) :=
  headerStates.map fun old =>
    ((mergeRegion plan).toGraph.run (Join.model model) 0 old).map fun bank => (bank.get result).toNat

/-- Report the actual body tag, counter and return slot at each activation. -/
def packets : List (Option (Nat × Nat × Nat)) :=
  headerStates.map fun old =>
    ((thetaBody plan).toGraph.run (Join.model model) 0 old).map fun
      | .cons tag bank => (tag.down.val, (bank.get count).toNat, (bank.get result).toNat)

/-- Inspect the actual numbered θ's two γs. Return the number of vertices
after the inner γ, both inner child lengths, and the outer false child length. -/
def layout : Option (Nat × List Nat × Nat) :=
  match lower plan with
  | .region nodes children _ =>
    let site := lastIndex (dataPorts regs) (source 0).body.producers
    if body : 0 < (nodes site).kind.arity then outerLayout (children site ⟨0, body⟩) else none
where
  innerLayout {args outs : List FixturePort} {sigs : List (List FixturePort)}
      (graph : Graph (Opcode Op) args [] sigs outs) : Option (Nat × List Nat) :=
    match graph with
    | .region nodes _ _ => do
      let gamma ← (List.finRange sigs.length).find? fun i => (nodes i).kind.arity == 2
      let lengths := (List.finRange (nodes gamma).kind.arity).map fun j => ((nodes gamma).childSigs j).length
      return (sigs.length - (gamma.val + 1), lengths)
  outerLayout {args outs : List FixturePort} {sigs : List (List FixturePort)}
      (graph : Graph (Opcode Op) args [] sigs outs) : Option (Nat × List Nat × Nat) :=
    match graph with
    | .region nodes children _ => do
      let gamma ← (List.finRange sigs.length).find? fun i => (nodes i).kind.arity == 2
      if two : 1 < (nodes gamma).kind.arity then
        let yes := children gamma ⟨0, Nat.lt_trans (by decide) two⟩
        let (after, inner) ← innerLayout yes
        return (after, inner, ((nodes gamma).childSigs ⟨1, two⟩).length)
      else none

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Example
