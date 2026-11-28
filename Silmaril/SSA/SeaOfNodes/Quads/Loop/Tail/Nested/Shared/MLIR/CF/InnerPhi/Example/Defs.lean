module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.Example.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Example.Defs

/-! # Observe both shared boundaries of the original 152 run -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi.Example

open Diamond.MLIR.CF.Example (input num regs result test)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Outer.Numbered.Example (headerStates plan)
open Outer.MLIR.CF.Phi (pack)
open Outer.MLIR.CF.Phi.Example (words)
open Outer.MLIR.CF.Phi.Readback (sameBank)
open Blocks (Bank)

abbrev routes := plan.toRoutes
def rows : Rows routes := (readRows routes).get (by rfl)

def takenInner (old : Bank (regs := regs) model) : Bool :=
  ((headerBank routes old).get routes.outerTest).down

def innerVisit (old : Bank (regs := regs) model) : Option ((Nat × Nat) × List Nat) := do
  if takenInner old then
    let taken := side routes old
    let edge := routes.innerEdgeOccurrence taken
    some ((edge.1.val, edge.2.val), words (pack (rows.bank taken input old)))
  else none

/-- Both boundaries observe the same three reached header activations. -/
def trace : List (Option ((Nat × Nat) × List Nat) × ((Nat × Nat) × List Nat)) :=
  (headerStates.map innerVisit).zip Outer.MLIR.CF.Phi.Example.selected

def gammaMatches : Bool := headerStates.all fun old =>
  if takenInner old then
    match (gamma routes).run (Join.model model) 0 (headerBank routes old) with
    | some bank => sameBank (rows.bank (side routes old) input old) (encodeValues bank)
    | none => false
  else true

/-- The inner-only profile can enter the shared segment directly from
both ordered successors of the same original split. -/
def parallelSource : Source Op regs num 8
  | 0 => ⟨(MLIR.CF.Example.source 0).body, .transfer (.jump 1)⟩
  | 1 => ⟨(MLIR.CF.Example.source 1).body, .branch test (.jump 2) (.jump 5)⟩
  | 2 => ⟨(MLIR.CF.Example.source 2).body, .branch test (.jump 3) (.jump 3)⟩
  | 3 => ⟨(MLIR.CF.Example.source 5).body, .transfer (.jump 4)⟩
  | 4 => ⟨(MLIR.CF.Example.source 6).body, .transfer (.jump 6)⟩
  | 5 => ⟨(MLIR.CF.Example.source 7).body, .transfer (.jump 6)⟩
  | 6 => ⟨(MLIR.CF.Example.source 8).body, .transfer (.jump 7)⟩
  | _ => ⟨(MLIR.CF.Example.source 9).body, .branch test (.jump 1) (.ret result)⟩

def parallelPlan : Shared.Program parallelSource 0 := (Shared.check parallelSource 0).get (by rfl)

abbrev parallelRoutes := Prefix.ofProgram parallelPlan

def parallelRows : Rows parallelRoutes := (readRows parallelRoutes).get (by rfl)

def parallelColumns : List ((Nat × Nat) × List Nat) :=
  [true, false].map fun taken =>
    let edge := parallelRoutes.innerEdgeOccurrence taken
    ((edge.1.val, edge.2.val),
      (List.finRange _).map fun slot => (parallelRows.view.table.column (parallelRows.edge taken) slot).val)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi.Example
