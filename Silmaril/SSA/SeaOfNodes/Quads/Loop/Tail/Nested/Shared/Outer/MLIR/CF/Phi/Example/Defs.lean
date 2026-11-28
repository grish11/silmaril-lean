module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Example.Defs

/-! # Observe the two actual Φ rows and the three visits in the 152 fixture -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Example

open Diamond.MLIR.CF.Example (input num regs)
open Outer.Numbered.Example (headerStates plan source)
open SeaOfNodes.Loop.MLIR.CF (Op)
open Silmaril.Isotope (Value)
open Silmaril.MLIR.Arith (Atom)

def rows : Rows plan := (readRows plan).get (by rfl)

def origin (taken : Bool) : Nat × Nat :=
  let edge := plan.outerEdgeOccurrence taken
  (edge.1.val, edge.2.val)

/-- Indices into each real post-body CF scope, in destination argument order. -/
def columns : List ((Nat × Nat) × List Nat) :=
  [true, false].map fun taken =>
    (origin taken, (List.finRange _).map fun i => (rows.view.table.column (rows.edge taken) i).val)

def words : Value Atom → List Nat
  | .pair (.atom ⟨_, v⟩) rest => v.toNat :: words rest
  | _ => []

def selected : List ((Nat × Nat) × List Nat) :=
  headerStates.map fun old => (origin (arrivalSide (p := plan) old), words (rows.latch input old))

/-- Let block 7 be the start of the outer shared tail, so the actual false
predecessor becomes the header's second successor rather than block 7. -/
def direct : Source Op regs num 12 := fun id =>
  if id = 6 then {source id with terminator := .transfer (.jump 7)} else source id

def directPlan : Program direct 0 := (Outer.check direct 0).get (by rfl)

def directRows : Rows directPlan := (readRows directPlan).get (by rfl)

def directSelected : List ((Nat × Nat) × List Nat) :=
  (headerStates.drop 2).map fun old =>
    let edge := directPlan.outerEdgeOccurrence (arrivalSide (p := directPlan) old)
    ((edge.1.val, edge.2.val), words (directRows.latch input old))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Example
