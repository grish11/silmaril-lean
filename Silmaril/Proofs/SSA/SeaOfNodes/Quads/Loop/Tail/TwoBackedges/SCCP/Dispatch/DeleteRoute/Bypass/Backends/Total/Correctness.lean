module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Worklist.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Proofs

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Tuple)

variable {regs : List (ValueSort Width)} {result : Width} {p : Program Op regs (.data result)}
variable [BankDecidableEq Word (dataPorts regs)] {facts : Tuple (Fact Word) (dataPorts regs)}

attribute [local irreducible] SCCP.solve

theorem compile_specialized_iff (targets : Backends.Targets p) :
    compile p facts = .specialized targets ↔ Backends.compile p facts = .ok targets := by
  rw [compile, Worklist.admit_eq_simultaneous, Backends.compile]
  cases admitted : Dispatch.admit model p facts with
  | ok checked => simp [Except.map]
  | error reason => cases reason <;> simp [Except.map]

theorem compile_twoLive_iff (targets : OriginalTargets p) :
    compile p facts = .twoLive targets ↔
      emitOriginal p = targets ∧
      incomingIndex (.feedback true) ∈ (solve model p facts).1 ∧
      incomingIndex (.feedback false) ∈ (solve model p facts).1 := by
  rw [compile, Worklist.admit_eq_simultaneous, ← Dispatch.admit_bothMarked_iff]
  cases admitted : Dispatch.admit model p facts with
  | ok checked => simp
  | error reason => cases reason <;> simp

theorem compile_neitherMarked_iff (targets : OriginalTargets p) :
    compile p facts = .neitherMarked targets ↔
      emitOriginal p = targets ∧
      incomingIndex (.feedback true) ∉ (solve model p facts).1 ∧
      incomingIndex (.feedback false) ∉ (solve model p facts).1 := by
  rw [compile, Worklist.admit_eq_simultaneous, ← Dispatch.admit_neitherMarked_iff]
  cases admitted : Dispatch.admit model p facts with
  | ok checked => simp
  | error reason => cases reason <;> simp

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Proofs
