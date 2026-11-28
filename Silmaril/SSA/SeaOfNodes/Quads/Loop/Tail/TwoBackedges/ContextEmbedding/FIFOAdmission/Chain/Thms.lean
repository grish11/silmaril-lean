module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Chain.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Chain.Checks
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Chain.Outcome

/-! Checked chain reports and exact one-shot outcomes under the staged write checks. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.CaptureChain

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open Silmaril.MLIR.Arith (Width)
open Composition (thenMap)
open Identification (PortMap program checkWrites pushFacts reduct)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted EntryFacts)
open Reindex.Guarded.Institution (AdmittedAt Generated Valuation)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {S T U : EntrySignature} {out : ValueSort Width} {result : Width}
variable {chain : CaptureChain S T} {seed : AdmittedAt S result}

theorem composite_append (left : CaptureChain S T) (right : CaptureChain T U) :
    (left.append right).composite = thenMap left.composite right.composite :=
  Proofs.composite_append left right

theorem reduct_append (left : CaptureChain S T) (right : CaptureChain T U) (input : Valuation U) :
    reduct (left.append right).composite input = reduct left.composite (reduct right.composite input) :=
  Proofs.reduct_append left right input

/-- Split the staged write checks at a typed intermediate signature. -/
theorem checkAllWrites_append (prefixChain : CaptureChain S T) (suffix : CaptureChain T U)
    (body : Program Op S.regs out) :
    (prefixChain.append suffix).checkAllWrites body =
      (prefixChain.checkAllWrites body && suffix.checkAllWrites (program prefixChain.composite body)) :=
  Proofs.checkAllWrites_append prefixChain suffix body

/-- The staged write checks imply the one-shot write check. -/
theorem composite_writes (chain : CaptureChain S T) (body : Program Op S.regs out)
    (checked : chain.checkAllWrites body = true) : checkWrites chain.composite body = true :=
  Proofs.composite_writes chain body checked

/-- A compatible write-safe suffix can only remove occurrence marks. -/
theorem marks_subset (chain : CaptureChain S T) (body : Program Op S.regs out)
    (checked : chain.checkAllWrites body = true) (oldFacts : EntryFacts S.regs)
    (newFacts : EntryFacts T.regs) (pushed : pushFacts chain.composite oldFacts = some newFacts) :
    (@SCCP.Worklist.solve _ _ _ _ model (program chain.composite body) T.bankEq newFacts).1 ⊆
      (@SCCP.Worklist.solve _ _ _ _ model body S.bankEq oldFacts).1 :=
  Proofs.marks_subset chain body checked oldFacts newFacts pushed

/-- Compare the composed suffix directly to the row recorded by the failed stage. -/
theorem FailedStage.suffix_marks_subset {result : Width} {map : PortMap S T} {seed : AdmittedAt S result}
    (failure : FailedStage map seed) (row : RefusedRow T result) (reported : failure.detail = .fifo row)
    (suffix : CaptureChain T U)
    (writes : suffix.checkAllWrites (program map (@Admitted.source _ _ S.bankEq seed)) = true)
    (facts : EntryFacts U.regs) (pushed : pushFacts suffix.composite row.facts = some facts) :
    (@SCCP.Worklist.solve _ _ _ _ model
      (program suffix.composite (program map (@Admitted.source _ _ S.bankEq seed))) U.bankEq facts).1 ⊆
      row.run.state.1 :=
  Proofs.suffix_marks_subset failure row reported suffix writes facts pushed

/-- The reported index belongs to the given chain. -/
theorem Report.firstFailure_lt (report : Report chain seed) {index : Nat} {reason : Identification.Refusal}
    (found : report.firstFailure = some (index, reason)) : index < chain.length :=
  Proofs.firstFailure_lt report found

/-- If every stage passed, the one-shot compiler returns the same last artifact. -/
theorem Report.compile_lastArtifact (report : Report chain seed) {artifact : Generated T result}
    (found : report.lastArtifact = some artifact) :
    Identification.compile chain.composite seed = .ok artifact :=
  Proofs.compile_lastArtifact report found

/-- The one-shot compiler preserves write, fact and FIFO precedence
when every raw stage passes its write check. -/
theorem Report.direct_of_failure (report : Report chain seed)
    (failed : report.firstFailure.isSome = true)
    (writes : chain.checkAllWrites (@Admitted.source _ _ S.bankEq seed) = true) :
    Identification.compile chain.composite seed =
      match pushFacts chain.composite (@Admitted.facts _ _ S.bankEq seed) with
      | none => .error .incompatibleFacts
      | some _ => .error (.checker .neitherMarked) :=
  Proofs.direct_of_failure report failed writes

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.CaptureChain
