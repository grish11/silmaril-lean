module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.Thms
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Thms

/-! The numbered and CF targets share the original word observation at matched budgets. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact TupleCovers)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Width Env)
open RVSDG (Tuple)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {result : Width}
variable {p : Program Op regs (.data result)} [BankDecidableEq Word (dataPorts regs)]
variable {facts : Tuple (Fact Word) (dataPorts regs)} {input : Bank (regs := regs) model}
variable {graph : Target p} {cfg : Bypass.MLIR.CF.Target regs result}

/-- One θ activation corresponds to one taken feedback visit. CF uses
two blocks per feedback plus the entry, first header and return block. -/
theorem compile_cf_run
    (numbered : compile model p facts = some graph) (cf : Bypass.MLIR.CF.compile p facts = some cfg)
    (covered : TupleCovers facts input) (fuel : Nat) :
    (graph.run (Join.model model) fuel input).map (fun result => Env.cons (result.get .head) .nil) =
      cfg.run evalOp (2 * fuel + 3) (encodeValues input) := by
  rw [compile_run numbered covered fuel, Bypass.MLIR.CF.compile_run cf covered fuel]
  cases p.source.runFrom model (3 * fuel + 2) 0 input <;> rfl

/-- Existential finite observations agree without choosing a common numerical budget. -/
theorem compile_cf_returns_iff
    (numbered : compile model p facts = some graph) (cf : Bypass.MLIR.CF.compile p facts = some cfg)
    (covered : TupleCovers facts input) (value : Word result) :
    graph.Returns (Join.model model) input (.cons value .nil) ↔
      ∃ fuel, cfg.run evalOp fuel (encodeValues input) = some (.cons value .nil) :=
  (compile_returns_iff numbered covered value).trans (Bypass.MLIR.CF.compile_returns_iff cf covered value).symm

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered
