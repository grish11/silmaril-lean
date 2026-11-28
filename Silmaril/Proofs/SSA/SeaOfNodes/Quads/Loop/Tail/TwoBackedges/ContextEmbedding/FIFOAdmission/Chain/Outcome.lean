module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Chain.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Chain.Checks
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Thms

/-! Compare actual staged reports to the compiler run on the composite port map. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.CaptureChain.Proofs

open Silmaril.MLIR.Arith (Width)
open Composition (thenMap)
open Identification (PortMap program checkWrites pushFacts)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted admit)
open Reindex.Guarded.Institution (AdmittedAt Generated)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {S T U : EntrySignature} {result : Width}
variable {chain : CaptureChain S T} {seed : AdmittedAt S result}

theorem firstFailure_lt (report : Report chain seed) {index : Nat} {reason : Identification.Refusal}
    (found : report.firstFailure = some (index, reason)) : index < chain.length := by
  induction report generalizing index reason with
  | done => simp [Report.firstFailure] at found
  | stopped failure =>
    have atZero := congrArg Prod.fst (Option.some.inj found)
    change 0 = index at atZero
    subst index
    exact Nat.zero_lt_succ _
  | passed emitted checked rest ih =>
    obtain ⟨⟨earlier, why⟩, hit, shifted⟩ := Option.map_eq_some_iff.mp found
    have step := congrArg Prod.fst shifted
    change earlier + 1 = index at step
    rw [← step, length]
    exact Nat.succ_lt_succ (ih hit)

theorem compile_lastArtifact (report : Report chain seed) {artifact : Generated T result}
    (found : report.lastArtifact = some artifact) :
    Identification.compile chain.composite seed = .ok artifact := by
  induction report with
  | done => simp [Report.lastArtifact] at found
  | stopped failure => simp [Report.lastArtifact] at found
  | @passed S M T head tail seed emitted checked rest ih =>
    cases tail with
    | nil =>
      cases rest with
      | done _ =>
        have same := Option.some.inj found
        exact checked.trans (congrArg Except.ok same)
    | cons next remaining =>
      have compiled := ih (by simpa [Report.lastArtifact] using found)
      have writes := (Identification.checkWrites_iff _ _).mpr (Identification.compile_safe _ _ compiled)
      exact (FactTransport.second_compile_eq head _ seed emitted checked writes).symm.trans compiled

private theorem fact_check_of_failure (head : PortMap S T) (seed : AdmittedAt S result)
    (writes : checkWrites head (@Admitted.source _ _ S.bankEq seed) = true)
    {reason : Identification.Refusal} (failed : Identification.compile head seed = .error reason) :
    reason ≠ .aliasedWrite ∧ (reason = .incompatibleFacts →
      pushFacts head (@Admitted.facts _ _ S.bankEq seed) = none) := by
  simp only [Identification.compile, Identification.replay, writes, ite_true] at failed
  cases pushed : pushFacts head (@Admitted.facts _ _ S.bankEq seed) with
  | none =>
    simp [pushed, Except.map] at failed
    subst reason
    simp
  | some facts =>
    rw [pushed] at failed
    cases admitted : @admit _ _ T.bankEq (program head (@Admitted.source _ _ S.bankEq seed)) facts with
    | ok _ => simp [admitted, Except.map] at failed
    | error _ =>
      simp [admitted, Except.map] at failed
      subst reason
      simp

private theorem direct_of_stopped (head : PortMap S T) (tail : CaptureChain T U)
    (seed : AdmittedAt S result) (failure : FailedStage head seed)
    (headWrites : checkWrites head (@Admitted.source _ _ S.bankEq seed) = true)
    (tailWrites : checkWrites tail.composite (program head (@Admitted.source _ _ S.bankEq seed)) = true) :
    Identification.compile (thenMap head tail.composite) seed =
      match pushFacts (thenMap head tail.composite) (@Admitted.facts _ _ S.bankEq seed) with
      | none => .error .incompatibleFacts
      | some _ => .error (.checker .neitherMarked) := by
  have rejected := failure.rejected
  obtain ⟨noAlias, factCheck⟩ := fact_check_of_failure head seed headWrites rejected
  cases why : failure.detail.reason with
  | aliasedWrite => exact (noAlias why).elim
  | incompatibleFacts =>
    have noFacts := factCheck why
    have finalNone :
        pushFacts (thenMap head tail.composite) (@Admitted.facts _ _ S.bankEq seed) = none := by
      rw [FactTransport.pushFacts_comp, noFacts]
      rfl
    have writes := (Identification.checkWrites_iff _ _).mpr <|
      Composition.safeWrites_thenMap head tail.composite _ ((Identification.checkWrites_iff _ _).mp headWrites)
        ((Identification.checkWrites_iff _ _).mp tailWrites)
    simp [Identification.compile, Identification.replay, writes, finalNone, Except.map]
  | checker reason =>
    rw [why] at rejected
    cases reason with
    | bothMarked => exact (compile_never_both head seed rejected).elim
    | neitherMarked => exact direct_of_neither head tail.composite seed rejected tailWrites

theorem direct_of_failure (report : Report chain seed)
    (failed : report.firstFailure.isSome = true)
    (writes : chain.checkAllWrites (@Admitted.source _ _ S.bankEq seed) = true) :
    Identification.compile chain.composite seed =
      match pushFacts chain.composite (@Admitted.facts _ _ S.bankEq seed) with
      | none => .error .incompatibleFacts
      | some _ => .error (.checker .neitherMarked) := by
  induction report with
  | done => simp [Report.firstFailure] at failed
  | @stopped S M T head tail seed failure =>
    simp only [checkAllWrites, Bool.and_eq_true] at writes
    exact direct_of_stopped head tail seed failure writes.1 (composite_writes tail _ writes.2)
  | @passed S M T head tail seed emitted checked rest ih =>
    simp only [checkAllWrites, Bool.and_eq_true] at writes
    have tailWrites := writes.2
    rw [← Identification.compile_source head seed checked] at tailWrites
    have tailSafe := composite_writes tail _ tailWrites
    have tailFailed : rest.firstFailure.isSome = true := by simpa [Report.firstFailure] using failed
    rw [composite, ← FactTransport.second_compile_eq head tail.composite seed emitted checked tailSafe,
      FactTransport.pushFacts_comp, Identification.compile_facts head seed checked]
    exact ih tailFailed tailWrites

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.CaptureChain.Proofs
