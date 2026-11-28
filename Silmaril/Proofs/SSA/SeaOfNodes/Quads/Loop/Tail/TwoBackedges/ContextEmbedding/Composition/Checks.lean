module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Transport
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Thms

/-! Distinguish the structural and fact checks from intermediate FIFO admission. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Proofs

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Diamond.SCCP (TupleCovers)
open SeaOfNodes.Loop.MLIR.CF (model)
open Silmaril.MLIR.Arith (Width)
open Blocks (Bank)
open Identification (BankMap PortMap pull program checkWrites pushFacts)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted EntryFacts admit)
open Reindex.Guarded.Institution (AdmittedAt)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {old middle new : List (ValueSort Width)}
variable {S T U : EntrySignature} {result : Width}

private theorem pushed_coverage (map : BankMap old new) (facts : EntryFacts old)
    (input : Bank (regs := new) model) :
    (∃ output, pushFacts map facts = some output ∧ TupleCovers output input) ↔
      TupleCovers facts (pull map input) := by
  cases ran : pushFacts map facts with
  | none => simp [Identification.pushFacts_refuses map facts ran input]
  | some output => simpa using Identification.pushFacts_covers map facts output ran input

theorem pushFacts_thenMap (first : BankMap old middle) (second : BankMap middle new)
    (facts : EntryFacts old) (input : Bank (regs := new) model) :
    (∃ direct, pushFacts (thenMap first second) facts = some direct ∧ TupleCovers direct input) ↔
      (∃ intermediate final, pushFacts first facts = some intermediate ∧
        pushFacts second intermediate = some final ∧ TupleCovers final input) := by
  rw [pushed_coverage, pull_thenMap, ← pushed_coverage first facts (pull second input)]
  constructor
  · rintro ⟨intermediate, ran, covered⟩
    obtain ⟨final, finished, holds⟩ := (pushed_coverage second intermediate input).mpr covered
    exact ⟨intermediate, final, ran, finished, holds⟩
  · rintro ⟨intermediate, final, ran, finished, holds⟩
    exact ⟨intermediate, ran, (pushed_coverage second intermediate input).mp ⟨final, finished, holds⟩⟩

theorem compileStaged_error_iff (first : PortMap S T) (second : Embedding T U)
    (p : AdmittedAt S result) (reason : Identification.Refusal) :
    compileStaged first second p = .error reason ↔ Identification.compile first p = .error reason := by
  cases ran : Identification.compile first p with
  | error => simp [compileStaged, ran]
  | ok intermediate =>
    simp [compileStaged, ran, second.compile_eq, Except.mapError]

theorem compileStaged_checker_iff (first : PortMap S T) (second : Embedding T U)
    (p : AdmittedAt S result) (reason : SCCP.Dispatch.Refusal) :
    compileStaged first second p = .error (.checker reason) ↔
      checkWrites first (@Admitted.source _ _ S.bankEq p) = true ∧
        ∃ facts, pushFacts first (@Admitted.facts _ _ S.bankEq p) = some facts ∧
          @admit _ _ T.bankEq (program first (@Admitted.source _ _ S.bankEq p)) facts = .error reason := by
  rw [compileStaged_error_iff]
  by_cases safe : checkWrites first (@Admitted.source _ _ S.bankEq p) = true
  · cases merged : pushFacts first (@Admitted.facts _ _ S.bankEq p) with
    | none => simp [Identification.compile, Identification.replay, safe, merged, Except.map]
    | some facts =>
      cases ran : @admit _ _ T.bankEq (program first (@Admitted.source _ _ S.bankEq p)) facts <;>
        simp [Identification.compile, Identification.replay, safe, merged, ran, Except.map]
  · simp [Identification.compile, Identification.replay, safe, Except.map]

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Proofs
