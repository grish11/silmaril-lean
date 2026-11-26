module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Boundaries.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi.Example.Defs

/-! # The two inner arrivals, the bypass, and the original θ result -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Example

open Diamond.MLIR.CF.Example (input regs width)
open SeaOfNodes.Loop.MLIR.CF (model)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open RVSDG.NestedTheta.Petri (Finishes)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Example (headerStates plan)
open Shared.MLIR.CF.InnerPhi (side)
open Blocks (Bank)

def activation (i : Fin 3) : Bank (regs := regs) model := headerStates[i.val]

def outerFixture (old : Bank (regs := regs) model) : Prop :=
  ∃ bank, OuterReads plan old bank ∧
    MLIR.CF.Phi.pack (encodeValues bank) = MLIR.CF.Phi.Example.rows.latch input old

def innerFixture (old : Bank (regs := regs) model) : Prop :=
  ∃ mark bank, Waiting plan old 0 mark ∧ readInner plan old 0 mark = some bank ∧
    encodeValues bank = Shared.MLIR.CF.InnerPhi.Example.rows.bank (side plan.toRoutes old) input old

def completion : Prop :=
  (∀ i : Fin 3, outerFixture (activation i)) ∧
    innerFixture (activation 0) ∧ innerFixture (activation 1) ∧
    (∃ mark, Waiting plan (activation 2) 1 mark ∧ readInner plan (activation 2) 1 mark = none) ∧
    Finishes semantics (lower plan) input (.cons (152 : Word width) .nil)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Example
