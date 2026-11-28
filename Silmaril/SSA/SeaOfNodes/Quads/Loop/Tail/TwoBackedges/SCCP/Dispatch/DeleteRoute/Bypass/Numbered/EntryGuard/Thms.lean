module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard.Coverage
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard.Correctness

/-! Selection and exact source observations for the emitted numbered graph. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact)
open SeaOfNodes.Loop.SCCP (BankDecidableEq decideTupleCovers)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Tuple)
open RVSDG.NestedTheta (Graph)
open Join (Opcode)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {result : Width} {p : Program Op regs (.data result)}
variable {outs : List (Diamond.Ty Width)}
variable {facts : Tuple (Fact Word) (dataPorts regs)} {target : Target regs result}

/-- The emitted selector's numbered run gives the certified coverage tag. -/
theorem selector_run [BankDecidableEq Word (dataPorts regs)]
    (facts : Tuple (Fact Word) (dataPorts regs)) (input : Bank (regs := regs) model) :
    (selector facts).2.toGraph.run (Join.model model) input =
      .cons ⟨index (@decide _ (decideTupleCovers facts input))⟩ .nil :=
  Proofs.selector_run facts input

/-- γ executes exactly the child named by the selector's result, with the
original bank in order and the child's original θ budget. -/
theorem attach_run (test : Selector regs) (childSigs : Fin 2 → List (List (Diamond.Ty Width)))
    (children : ∀ i, Graph (Opcode Op) (dataPorts regs) [] (childSigs i) outs)
    (fuel : Nat) (input : Bank (regs := regs) model) :
    (attach test childSigs children).run (Join.model model) fuel input =
      let selected := ((test.2.toGraph.run (Join.model model) input).get .head).down
      (children selected).run (Join.model model) fuel input :=
  Proofs.attach_run childSigs children test fuel input

variable [BankDecidableEq Word (dataPorts regs)]

/-- The selector and its enclosing γ consume no θ activations. -/
theorem compile_run (success : compile p facts = .ok target) (fuel : Nat)
    (input : Bank (regs := regs) model) :
    target.2.run (Join.model model) fuel input =
      (p.source.runFrom model (3 * fuel + 2) 0 input).map (fun value => .cons value .nil) :=
  Proofs.compile_run success fuel input

theorem compile_returns_iff (success : compile p facts = .ok target)
    (input : Bank (regs := regs) model) (value : Word result) :
    target.2.Returns (Join.model model) input (.cons value .nil) ↔
      ∃ fuel, p.source.runFrom model fuel 0 input = some value :=
  Proofs.compile_returns_iff success input value

theorem compile_noReturn_iff (success : compile p facts = .ok target) (input : Bank (regs := regs) model) :
    (∀ fuel, target.2.run (Join.model model) fuel input = none) ↔
      ¬ ∃ value fuel, p.source.runFrom model fuel 0 input = some value :=
  Proofs.compile_noReturn_iff success input

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard
