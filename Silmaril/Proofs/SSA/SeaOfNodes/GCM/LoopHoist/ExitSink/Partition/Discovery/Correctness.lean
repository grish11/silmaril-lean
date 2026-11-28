module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery.Defs

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Block)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist (Label)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier (operations)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (TargetOp)

variable {extra Γ : List Width} {saved carried result : Width}
variable {code : Block TargetOp (Label saved carried result extra) Γ [result]}
variable {scan : Scan} {mask : List Bool} {reads : List Nat}

theorem scan_closed (found : scan? code = some scan) : RetainedReads code scan.mask scan.inputs := by
  induction code generalizing scan with
  | terminator term =>
    obtain ⟨roots, taken, rfl⟩ := Option.map_eq_some_iff.mp found
    exact .finish taken
  | letOp op operands tail ih =>
    obtain ⟨report, taken, rfl⟩ := Option.map_eq_some_iff.mp found
    have valid := ih taken
    by_cases used : 0 ∈ report.inputs
    · simpa [Scan.beforeBinding, used] using
        RetainedReads.keep (op := op) (operands := operands) valid
    · simpa [Scan.beforeBinding, used] using
        RetainedReads.move (op := op) (operands := operands) valid used

private theorem retained_length (valid : RetainedReads code mask reads) : mask.length = (operations code).length := by
  induction valid with
  | finish => rfl
  | keep _ ih => simp only [List.length_cons, operations, ih]
  | move _ _ ih => simp only [List.length_cons, operations, ih]

theorem scan_length (found : scan? code = some scan) : scan.mask.length = (operations code).length :=
  retained_length (scan_closed found)

private theorem older_mono {small large : List Nat}
    (contained : ∀ read ∈ small, read ∈ large) :
    ∀ read ∈ older small, read ∈ older large := by
  intro read present
  obtain ⟨newer, listed, mapped⟩ := List.mem_filterMap.mp present
  exact List.mem_filterMap.mpr ⟨newer, contained newer listed, mapped⟩

theorem scan_least (valid : RetainedReads code mask reads) (found : scan? code = some scan) :
    (∀ read ∈ scan.inputs, read ∈ reads) ∧
    ∀ index : Nat, mask[index]? = some true → scan.mask[index]? = some true := by
  induction valid generalizing scan with
  | finish root =>
    simp only [scan?, root, Option.map_some, Option.some.injEq] at found
    cases found
    exact ⟨fun _ listed => listed, fun _ wanted => by simp at wanted⟩
  | keep valid ih =>
    obtain ⟨report, taken, rfl⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨needed, moves⟩ := ih taken
    by_cases used : 0 ∈ report.inputs
    · simp only [Scan.beforeBinding, ite_eq_left used]
      refine ⟨?_, ?_⟩
      · intro read present
        rcases List.mem_append.mp present with olderRead | operand
        · exact List.mem_append_left _ (older_mono needed read olderRead)
        · exact List.mem_append_right _ operand
      · intro index moved
        cases index with
        | zero => simp at moved
        | succ index => exact moves index moved
    · simp only [Scan.beforeBinding, ite_eq_right used]
      refine ⟨fun read present => List.mem_append_left _ (older_mono needed read present), ?_⟩
      intro index moved
      cases index with
      | zero => rfl
      | succ index => exact moves index moved
  | move valid unused ih =>
    obtain ⟨report, taken, rfl⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨needed, moves⟩ := ih taken
    have safe : 0 ∉ report.inputs := fun used => unused (needed 0 used)
    simp only [Scan.beforeBinding, ite_eq_right safe]
    refine ⟨older_mono needed, ?_⟩
    intro index moved
    cases index with
    | zero => rfl
    | succ index => exact moves index moved

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery
