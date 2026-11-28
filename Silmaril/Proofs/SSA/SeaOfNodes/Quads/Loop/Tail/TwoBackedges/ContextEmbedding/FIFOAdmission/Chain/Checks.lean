module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Chain.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.WriteAdmission.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Thms

/-! Fold the existing write and fact refinement checks through a typed chain. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.CaptureChain.Proofs

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open Silmaril.MLIR.Arith (Width)
open Identification (PortMap checkWrites program pushFacts reduct)
open Composition (thenMap)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted EntryFacts)
open Reindex.Guarded.Institution (AdmittedAt Valuation)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {S T U : EntrySignature} {out : ValueSort Width}

theorem composite_append (left : CaptureChain S T) (right : CaptureChain T U) :
    (left.append right).composite = thenMap left.composite right.composite := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
    simp only [append, composite, ih]
    rfl

theorem reduct_append (left : CaptureChain S T) (right : CaptureChain T U) (input : Valuation U) :
    reduct (left.append right).composite input = reduct left.composite (reduct right.composite input) := by
  rw [composite_append, Composition.reduct_thenMap]

theorem checkAllWrites_append (prefixChain : CaptureChain S T) (suffix : CaptureChain T U)
    (body : Program Op S.regs out) :
    (prefixChain.append suffix).checkAllWrites body =
      (prefixChain.checkAllWrites body && suffix.checkAllWrites (program prefixChain.composite body)) := by
  induction prefixChain with
  | nil =>
    simpa only [append, checkAllWrites, composite, Bool.true_and] using
      congrArg suffix.checkAllWrites (Composition.program_identity body).symm
  | cons head tail ih =>
    simp only [append, checkAllWrites, composite, ih, Composition.program_thenMap, Bool.and_assoc]

theorem composite_writes (chain : CaptureChain S T) (body : Program Op S.regs out)
    (checked : chain.checkAllWrites body = true) : checkWrites chain.composite body = true := by
  induction chain with
  | nil =>
    exact (Identification.checkWrites_iff _ _).mpr (fun _ _ _ _ same => same)
  | cons head tail ih =>
    simp only [checkAllWrites, Bool.and_eq_true] at checked
    have both : (checkWrites head body && checkWrites tail.composite (program head body)) = true := by
      simp only [Bool.and_eq_true]
      exact ⟨checked.1, ih _ checked.2⟩
    rw [WriteAdmission.staged_checks_eq] at both
    simp only [Bool.and_eq_true] at both
    exact both.1

/-- The composed suffix cannot introduce any mark, including entry and exit.
The input block is the actual successful intersection at its final signature. -/
theorem marks_subset (chain : CaptureChain S T) (body : Program Op S.regs out)
    (checked : chain.checkAllWrites body = true) (oldFacts : EntryFacts S.regs)
    (newFacts : EntryFacts T.regs) (pushed : pushFacts chain.composite oldFacts = some newFacts) :
    (@SCCP.Worklist.solve _ _ _ _ model (program chain.composite body) T.bankEq newFacts).1 ⊆
      (@SCCP.Worklist.solve _ _ _ _ model body S.bankEq oldFacts).1 :=
  fifo_marks_subset chain.composite body ((Identification.checkWrites_iff _ _).mp
    (composite_writes chain body checked)) oldFacts newFacts (FactTransport.pushFacts_refines _ _ _ pushed)

theorem suffix_marks_subset {result : Width} {map : PortMap S T} {seed : AdmittedAt S result}
    (failure : FailedStage map seed) (row : RefusedRow T result) (reported : failure.detail = .fifo row)
    (suffix : CaptureChain T U)
    (writes : suffix.checkAllWrites (program map (@Admitted.source _ _ S.bankEq seed)) = true)
    (facts : EntryFacts U.regs) (pushed : pushFacts suffix.composite row.facts = some facts) :
    (@SCCP.Worklist.solve _ _ _ _ model
      (program suffix.composite (program map (@Admitted.source _ _ S.bankEq seed))) U.bankEq facts).1 ⊆
      row.run.state.1 := by
  have diagnosed := failure.diagnosed
  rw [reported] at diagnosed
  have inspected := (fifo_of_diagnose map seed row diagnosed).2.2
  rw [(inspect_row _ _ row inspected).1]
  exact marks_subset suffix _ writes row.facts facts pushed

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.CaptureChain.Proofs
