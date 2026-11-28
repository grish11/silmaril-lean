module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Observation.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Observation.Correctness

/-! One end-to-end observation theorem independent of the outcome tag. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact TupleCovers)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open SeaOfNodes.Loop.MLIR.CF (Op TargetOp model evalOp)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Tail.Diamond.MLIR.CF (Widths)
open RVSDG.NestedTheta (Graph)
open RVSDG (Tuple)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {result : Width} {p : Program Op regs (.data result)}
variable {facts : Tuple (Fact Word) (dataPorts regs)} {outcome : Outcome p}
variable {execution : Execution regs result}
variable {input : Bank (regs := regs) model}

theorem Outcome.compatible_of_covers (outcome : Outcome p) (covered : TupleCovers facts input) :
    outcome.Compatible facts input := by
  cases outcome <;> first | exact covered | trivial

/-- A compiled outcome has the original source's matched-budget and
finite-return observations on every compatible typed input. -/
theorem compile_correct [BankDecidableEq Word (dataPorts regs)]
    (compiled : compile p facts = outcome) (compatible : outcome.Compatible facts input) :
    Correct outcome input :=
  Observation.Proofs.compile_correct compiled compatible

/-- View the original outcome proof as correctness of its two artifacts. -/
theorem Correct.asExecution (correct : Correct outcome input) : outcome.execution.Correct p input :=
  ⟨correct.bounded, correct.returns_iff⟩

/-- The unmodified backends agree with the source at any typed input. -/
theorem original_correct : (emitOriginal p).execution.Correct p input :=
  Observation.Proofs.original_correct

/-- Absence of a finite return is equivalent across all three runners. -/
theorem Execution.Correct.noReturn_iff (correct : execution.Correct p input) :
    let absent := ¬ ∃ value budget, runSource p input budget = some value
    ((∀ budget, execution.runCF input budget = none) ↔ absent) ∧
      ((∀ budget, execution.runNumbered input budget = none) ↔ absent) :=
  Observation.Proofs.noReturn_iff correct

theorem Correct.noReturn_iff (correct : Correct outcome input) :
    let absent := ¬ ∃ value budget, runSource p input budget = some value
    ((∀ budget, outcome.runCF input budget = none) ↔ absent) ∧
      ((∀ budget, outcome.runNumbered input budget = none) ↔ absent) :=
  correct.asExecution.noReturn_iff

theorem mem_sourcePart_iff {value : Word result} :
    value ∈ sourcePart p input ↔ ∃ budget, runSource p input budget = some value :=
  Observation.Proofs.mem_sourcePart_iff

/-- Membership in the pure CF observer has an independent block-fuel witness. -/
theorem mem_observeCF_iff {Label : List Width → Type}
    (target : Cfg TargetOp Label (Widths regs) [result]) {value : Word result} :
    value ∈ observeCF target input ↔
      ∃ fuel, target.run evalOp fuel (encodeValues input) = some (.cons value .nil) :=
  Observation.Proofs.mem_observeCF_iff target

/-- Membership in the numbered observer is an exact finite return. -/
theorem mem_observeNumbered_iff {sigs}
    (target : Graph (Join.Opcode Op) (dataPorts regs) [] sigs [.value (.data result)])
    {value : Word result} :
    value ∈ observeNumbered target input ↔ target.Returns (Join.model model) input (.cons value .nil) :=
  Observation.Proofs.mem_observeNumbered_iff target

/-- The actual partial target denotations, projected to their one result word,
agree with the source's unbounded return observation. -/
theorem Execution.Correct.part_eq (correct : execution.Correct p input) :
    execution.cfPart input = sourcePart p input ∧ execution.numberedPart input = sourcePart p input :=
  Observation.Proofs.part_eq correct

theorem Correct.part_eq (correct : Correct outcome input) :
    outcome.cfPart input = sourcePart p input ∧ outcome.numberedPart input = sourcePart p input :=
  correct.asExecution.part_eq

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total
