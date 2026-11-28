module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Facts
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Thms

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Worklist.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.Thms

/-! The FIFO observes the same marks when the final map is an embedding. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Proofs

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open Silmaril.MLIR.Arith (Width)
open Identification (program)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted EntryFacts admit)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Worklist (admit_eq_simultaneous)
open Reindex.Guarded.Institution (AdmittedAt)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {S T : EntrySignature} {out : ValueSort Width} {result : Width}

set_option backward.isDefEq.respectTransparency false in
theorem solve_marks (path : Embedding S T) (p : Program Op S.regs out) (facts : EntryFacts S.regs) :
    (@SCCP.solve _ _ _ _ model (program path.portMap p) T.bankEq (embedFacts path facts)).1 =
      (@SCCP.solve _ _ _ _ model p S.bankEq facts).1 := by
  induction path with
  | id A =>
    change (@SCCP.solve _ _ _ _ model (program (fun _ port => port) p) A.bankEq facts).1 = _
    rw [Composition.program_identity]
  | @permute A B C order rest ih =>
    have body :
        program (Embedding.permute order rest).portMap p = program rest.portMap (Reindex.program order p) :=
      (Composition.program_thenMap (fun t => order t) rest.portMap p).symm
    rw [body, embedFacts, ih]
    exact congrArg Prod.fst (@Reindex.solve_assignment _ _ _ _ _ order model p A.bankEq B.bankEq facts)
  | @weaken A C fresh rest ih =>
    have body :
        program (Embedding.weaken fresh rest).portMap p = program rest.portMap (Weakening.program fresh p) :=
      (Composition.program_thenMap (middle := fresh :: A.regs) (fun _ port => .tail port) rest.portMap p).symm
    rw [body, embedFacts, ih]
    exact congrArg Prod.fst (@Weakening.solve_project _ _ _ _ _ model p A.bankEq
      (Weakening.Guarded.captureEq fresh) facts)

theorem fifo_marks (path : Embedding S T) (p : Program Op S.regs out) (facts : EntryFacts S.regs) :
    (@SCCP.Worklist.solve _ _ _ _ model (program path.portMap p) T.bankEq (embedFacts path facts)).1 =
      (@SCCP.Worklist.solve _ _ _ _ model p S.bankEq facts).1 := by
  rw [SCCP.Worklist.solve_eq_simultaneous, SCCP.Worklist.solve_eq_simultaneous]
  exact solve_marks path p facts

private theorem admit_error_iff (p : Program Op S.regs (.data result)) (facts : EntryFacts S.regs)
    (reason : SCCP.Dispatch.Refusal) :
    @admit _ _ S.bankEq p facts = .error reason ↔
      @SCCP.Dispatch.admit _ _ _ _ model p S.bankEq facts = .error reason := by
  rw [← admit_eq_simultaneous]
  unfold admit
  split <;> simp_all

theorem admit_embedding (path : Embedding S T) (p : Program Op S.regs (.data result)) (facts : EntryFacts S.regs) :
    @admit _ _ T.bankEq (program path.portMap p) (embedFacts path facts) =
      (@admit _ _ S.bankEq p facts).map path.mapAdmitted := by
  cases ran : @admit _ _ S.bankEq p facts with
  | error reason =>
    change @admit _ _ T.bankEq (program path.portMap p) (embedFacts path facts) = .error reason
    apply (admit_error_iff _ _ reason).mpr
    have mid := (admit_error_iff p facts reason).mp ran
    cases reason with
    | bothMarked =>
      apply (@SCCP.Dispatch.admit_bothMarked_iff _ _ _ _ model _ T.bankEq _).mpr
      rw [solve_marks path p facts]
      exact (@SCCP.Dispatch.admit_bothMarked_iff _ _ _ _ model p S.bankEq facts).mp mid
    | neitherMarked =>
      apply (@SCCP.Dispatch.admit_neitherMarked_iff _ _ _ _ model _ T.bankEq _).mpr
      rw [solve_marks path p facts]
      exact (@SCCP.Dispatch.admit_neitherMarked_iff _ _ _ _ model p S.bankEq facts).mp mid
  | ok accepted =>
    change @admit _ _ T.bankEq (program path.portMap p) (embedFacts path facts) =
      .ok (path.mapAdmitted accepted)
    obtain ⟨code, guard⟩ := Identification.admit_fields p facts accepted ran
    have codeEq := (Composition.embedding_source path accepted).trans (congrArg (program path.portMap) code)
    have factsEq := (mapped_facts path accepted).trans (congrArg (embedFacts path) guard)
    rw [← codeEq, ← factsEq]
    exact @Admitted.admit_self _ _ T.bankEq (path.mapAdmitted accepted)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Proofs
