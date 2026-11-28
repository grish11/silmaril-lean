module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Proofs

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Tuple)

variable {regs : List (ValueSort Width)} {result : Width}
variable {p : Program Op regs (.data result)} [BankDecidableEq Word (dataPorts regs)]
variable {facts : Tuple (Fact Word) (dataPorts regs)} {targets : Targets p}

attribute [local irreducible] SCCP.solve

theorem compile_components (success : compile p facts = .ok targets) :
    Bypass.MLIR.CF.compile p facts = some targets.cf ∧
      Numbered.compile model p facts = some targets.numbered ∧
      incomingIndex (.feedback targets.retained) ∈ (solve model p facts).1 ∧
      incomingIndex (.feedback !targets.retained) ∉ (solve model p facts).1 := by
  cases admitted : admit model p facts with
  | error reason => simp [compile, admitted, Except.map] at success
  | ok checked =>
    have emitted : ⟨checked.side, Bypass.MLIR.CF.lower checked, Numbered.lower checked⟩ = targets := by
      simpa [compile, admitted, Except.map, emit] using success
    subst targets
    have accepted : check model p facts = some checked := by rw [check, admitted]; rfl
    exact ⟨congrArg (Option.map Bypass.MLIR.CF.lower) accepted,
      congrArg (Option.map Numbered.lower) accepted, checked.marked, checked.excluded⟩

theorem compile_error_iff (reason : Refusal) :
    compile p facts = .error reason ↔
      match reason with
      | .bothMarked =>
        incomingIndex (.feedback true) ∈ (solve model p facts).1 ∧
          incomingIndex (.feedback false) ∈ (solve model p facts).1
      | .neitherMarked =>
        incomingIndex (.feedback true) ∉ (solve model p facts).1 ∧
          incomingIndex (.feedback false) ∉ (solve model p facts).1 := by
  have same : compile p facts = .error reason ↔ admit model p facts = .error reason := by
    cases admitted : admit model p facts <;> simp [compile, admitted, Except.map]
  cases reason with
  | bothMarked => exact same.trans admit_bothMarked_iff
  | neitherMarked => exact same.trans admit_neitherMarked_iff

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Proofs
