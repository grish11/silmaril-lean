module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Worklist.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.Thms

/-! Relate the diagnostic to the actual compiler, with exact drained-row evidence. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Proofs

open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.Loop.SCCP (bankTuple)
open Silmaril.MLIR.Arith (Width)
open Identification (PortMap checkWrites program pushFacts)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted EntryFacts admit)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Worklist renaming admit → fifoAdmit
open Reindex.Guarded.Institution (AdmittedAt)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {S T : EntrySignature} {result : Width}

private theorem inspect_erases (code : Program Op T.regs (.data result)) (facts : EntryFacts T.regs) :
    (inspect T code facts).mapError RefusedRow.reason =
      (@fifoAdmit _ _ _ _ model T.bankEq code facts).map (fun _ => ()) := by
  dsimp only [inspect, fifoAdmit, SCCP.Worklist.solve]
  split <;> simp_all [Except.mapError, Except.map]

private theorem guarded_erases (code : Program Op T.regs (.data result)) (facts : EntryFacts T.regs) :
    (@admit _ _ T.bankEq code facts).map (fun _ => ()) =
      (@fifoAdmit _ _ _ _ model T.bankEq code facts).map (fun _ => ()) := by
  dsimp only [admit]
  split <;> simp_all [Except.map]

theorem diagnose_compile (map : PortMap S T) (seed : AdmittedAt S result) :
    (diagnose map seed).mapError Refusal.reason = (Identification.compile map seed).map (fun _ => ()) := by
  by_cases writes : checkWrites map (@Admitted.source _ _ S.bankEq seed) = true
  · cases pushed : pushFacts map (@Admitted.facts _ _ S.bankEq seed) with
    | none => simp [diagnose, Identification.compile, Identification.replay, writes, pushed, Except.map,
        Except.mapError, Refusal.reason]
    | some facts =>
      simp only [diagnose, Identification.compile, Identification.replay, writes, ite_true, pushed]
      let code := program map (@Admitted.source _ _ S.bankEq seed)
      have same := (inspect_erases (T := T) code facts).trans (guarded_erases (T := T) code facts).symm
      change ((inspect T code facts).mapError Refusal.fifo).mapError Refusal.reason = _
      change _ = ((match @admit _ _ T.bankEq code facts with
        | .error reason => Except.error (Identification.Refusal.checker reason)
        | .ok seed => Except.ok seed).map Reindex.Guarded.Institution.Generated.lower).map (fun _ => ())
      cases observed : inspect T code facts <;>
        cases checked : @admit _ _ T.bankEq code facts <;>
        simp_all [Except.mapError, Except.map, Refusal.reason]

  · simp [diagnose, Identification.compile, Identification.replay, writes, Except.map, Except.mapError, Refusal.reason]

theorem fifo_of_diagnose (map : PortMap S T) (seed : AdmittedAt S result)
    (row : RefusedRow T result) (ran : diagnose map seed = .error (.fifo row)) :
    checkWrites map (@Admitted.source _ _ S.bankEq seed) = true ∧
      pushFacts map (@Admitted.facts _ _ S.bankEq seed) = some row.facts ∧
      inspect T (program map (@Admitted.source _ _ S.bankEq seed)) row.facts = .error row := by
  by_cases writes : checkWrites map (@Admitted.source _ _ S.bankEq seed) = true
  · cases pushed : pushFacts map (@Admitted.facts _ _ S.bankEq seed) with
    | none => simp [diagnose, writes, pushed] at ran
    | some facts =>
      simp only [diagnose, writes, ite_true, pushed] at ran
      cases hit : inspect T (program map (@Admitted.source _ _ S.bankEq seed)) facts with
      | ok => simp [hit, Except.mapError] at ran
      | error found =>
        simp only [hit, Except.mapError, Except.error.injEq, Refusal.fifo.injEq] at ran
        subst found
        have same : facts = row.facts := by
          dsimp only [inspect] at hit
          split at hit <;> cases hit
          rfl
        subst facts
        exact ⟨writes, rfl, hit⟩
  · simp [diagnose, writes] at ran

theorem inspect_row (source : Program Op T.regs (.data result)) (facts : EntryFacts T.regs)
    (row : RefusedRow T result) (found : inspect T source facts = .error row) :
    row.run = @SCCP.Worklist.run _ _ _ _ model source T.bankEq facts ∧ row.run.pending = [] ∧
      row.continuation = (SCCP.blockFacts model source.header (bankTuple row.run.state.2.1)).get source.again ∧
      row.selector = (SCCP.blockFacts model source.header (bankTuple row.run.state.2.1)).get source.select ∧
      Refuses row.run.state.1 row.reason := by
  let _ := T.bankEq
  dsimp only [inspect] at found
  split at found
  · cases found
  · rename_i reason checked
    cases found
    refine ⟨rfl, @SCCP.Worklist.run_drains _ _ _ _ model T.bankEq source facts, rfl, rfl, ?_⟩
    rw [SCCP.Dispatch.admitWith_eq] at checked
    cases reason with
    | bothMarked =>
      simpa only [← SCCP.Worklist.solve_eq_simultaneous model source facts, SCCP.Worklist.solve, Refuses] using
        (SCCP.Dispatch.admit_bothMarked_iff.mp checked)
    | neitherMarked =>
      simpa only [← SCCP.Worklist.solve_eq_simultaneous model source facts, SCCP.Worklist.solve, Refuses] using
        (SCCP.Dispatch.admit_neitherMarked_iff.mp checked)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Proofs
