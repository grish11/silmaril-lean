module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Solver
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Facts
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Thms

/-! Exact replay and emitted artifact agreement for the embedding suffix. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Proofs

open Silmaril.MLIR.Arith (Width)
open Composition (thenMap)
open Identification (PortMap Refusal checkWrites pushFacts program)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted admit)
open Reindex.Guarded.Institution (AdmittedAt Generated)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {S T U : EntrySignature} {result : Width}

theorem replay_compose (first : PortMap S T) (path : Embedding T U) (p : AdmittedAt S result) :
    Identification.replay (thenMap first path.portMap) p =
      (Identification.replay first p).map path.mapAdmitted := by
  simp only [Identification.replay, Composition.checkWrites_embedding, pushFacts_embedding]
  split
  · cases pushed : pushFacts first (@Admitted.facts _ _ S.bankEq p) with
    | none => rfl
    | some facts =>
      rw [← Composition.program_thenMap first path.portMap]
      simp only [Option.map_some, admit_embedding]
      cases @admit _ _ T.bankEq (program first (@Admitted.source _ _ S.bankEq p)) facts <;> rfl
  · rfl

theorem compile_direct_eq_staged (first : PortMap S T) (path : Embedding T U) (p : AdmittedAt S result) :
    Identification.compile (thenMap first path.portMap) p = Composition.compileStaged first path p := by
  rw [Identification.compile, replay_compose]
  cases ran : Identification.replay first p with
  | error =>
    simp only [Composition.compileStaged, Identification.compile, ran, Except.map]
  | ok accepted =>
    simp only [Composition.compileStaged, Identification.compile, ran, Except.map,
      path.compile_eq, path.mapGenerated_lower, Except.mapError]
    rfl

private theorem compile_embedding (path : Embedding S T) (p : AdmittedAt S result)
    (fixed : pushFacts (fun _ port => port) (@Admitted.facts _ _ S.bankEq p) =
      some (@Admitted.facts _ _ S.bankEq p)) :
    Identification.compile path.portMap p = (path.compile p).mapError Refusal.checker := by
  let identity : PortMap S S := fun _ port => port
  have writes : checkWrites identity (@Admitted.source _ _ S.bankEq p) = true :=
    (Identification.checkWrites_iff _ _).mpr (Identification.embedding_safe (.id S) _)
  have facts : pushFacts identity (@Admitted.facts _ _ S.bankEq p) =
      some (@Admitted.facts _ _ S.bankEq p) := fixed
  have body : program identity (@Admitted.source _ _ S.bankEq p) = @Admitted.source _ _ S.bankEq p :=
    Composition.program_identity _
  have firstOk : Identification.compile identity p = .ok (Generated.lower p) := by
    simp only [Identification.compile, Identification.replay, writes, ite_true, facts, body,
      Admitted.admit_self, Except.map]
  change Identification.compile (thenMap identity path.portMap) p = _
  rw [compile_direct_eq_staged, Composition.compileStaged, firstOk]
  rfl

theorem compare_embedding (first : PortMap S T) (path : Embedding T U) (p : AdmittedAt S result) :
    (LiftComposition.compare first path.portMap p).map (fun q => (q.staged, q.direct)) =
      ((Identification.compile (thenMap first path.portMap) p).map (fun q => (q, q))).mapError
        LiftComposition.Refused.first := by
  cases ran : Identification.compile first p with
  | error reason =>
    have direct : Identification.compile (thenMap first path.portMap) p = .error reason := by
      rw [compile_direct_eq_staged, Composition.compileStaged, ran]
    rw [direct]
    unfold LiftComposition.compare
    split <;> simp_all [Except.map, Except.mapError]
  | ok mid =>
    have second := compile_embedding path mid.source
      (push_id_of_push _ _ _ (Identification.compile_facts first p ran))
    have staged :
        (path.compile mid.source).mapError Refusal.checker = .ok (path.mapGenerated (Generated.lower mid.source)) := by
      rw [path.compile_eq]
      rfl
    have direct : Identification.compile (thenMap first path.portMap) p =
        .ok (path.mapGenerated (Generated.lower mid.source)) := by
      rw [compile_direct_eq_staged, Composition.compileStaged, ran]
      exact staged
    have secondOk := second.trans staged
    rw [direct]
    unfold LiftComposition.compare
    split
    · rename_i reason rejected
      cases (rejected.symm.trans ran)
    · rename_i intermediate accepted
      have same := Except.ok.inj (accepted.symm.trans ran)
      subst intermediate
      split
      · rename_i reason rejected
        cases (rejected.symm.trans secondOk)
      · rename_i emitted secondRan
        have same := Except.ok.inj (secondRan.symm.trans secondOk)
        subst emitted
        split
        · rename_i reason rejected
          cases (rejected.symm.trans direct)
        · rename_i emitted directRan
          have same := Except.ok.inj (directRan.symm.trans direct)
          subst emitted
          rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Proofs
