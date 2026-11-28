module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.CheckedEntry.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Observation.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.CheckedEntry.Proofs

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {result : Width} {p : Program Op regs (.data result)}

theorem dispatch_correct [BankDecidableEq Word (dataPorts regs)] (prepared : Prepared p)
    (input : Bank (regs := regs) model) : (dispatch prepared input).execution.Correct p input := by
  obtain ⟨facts, outcome, compiled⟩ := prepared
  cases outcome with
  | specialized targets =>
    simp only [dispatch]
    split
    · rename_i covered
      exact (Total.compile_correct compiled covered).asExecution
    · exact original_correct
  | twoLive targets => exact (Total.compile_correct compiled trivial).asExecution
  | neitherMarked targets => exact (Total.compile_correct compiled trivial).asExecution

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.CheckedEntry.Proofs
