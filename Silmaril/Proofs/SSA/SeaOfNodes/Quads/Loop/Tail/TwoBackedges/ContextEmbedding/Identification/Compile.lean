module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Native
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Facts

/-! Invert success at the real replay boundary. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Proofs

open SeaOfNodes.Diamond.SCCP (TupleCovers)
open SeaOfNodes.Loop.MLIR.CF (Op)
open Silmaril.MLIR.Arith (Width)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted EntryFacts admit)
open Reindex.Guarded.Institution (AdmittedAt Generated Valuation)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {S T : EntrySignature} {result : Width}

theorem admit_fields (p : Program Op T.regs (.data result)) (facts : EntryFacts T.regs)
    (target : AdmittedAt T result) (ok : @admit _ _ T.bankEq p facts = .ok target) :
    @Admitted.source _ _ T.bankEq target = p ∧ @Admitted.facts _ _ T.bankEq target = facts := by
  unfold admit at ok
  split at ok
  · cases Except.ok.inj ok
    exact ⟨rfl, rfl⟩
  · cases ok

private theorem replay_ok (map : PortMap S T) (p : AdmittedAt S result) (target : AdmittedAt T result)
    (ok : replay map p = .ok target) :
    SafeWrites map (@Admitted.source _ _ S.bankEq p) ∧
      ∃ facts, pushFacts map (@Admitted.facts _ _ S.bankEq p) = some facts ∧
        @admit _ _ T.bankEq (program map (@Admitted.source _ _ S.bankEq p)) facts = .ok target := by
  by_cases safe : checkWrites map (@Admitted.source _ _ S.bankEq p) = true
  · simp only [replay, safe, ite_true] at ok
    cases merged : pushFacts map (@Admitted.facts _ _ S.bankEq p) with
    | none =>
      rw [merged] at ok
      cases ok
    | some facts =>
      rw [merged] at ok
      change (match @admit _ _ T.bankEq (program map (@Admitted.source _ _ S.bankEq p)) facts with
        | .error reason => (Except.error (Refusal.checker reason) : Except Refusal (AdmittedAt T result))
        | .ok checked => Except.ok checked) = Except.ok target at ok
      cases ran : @admit _ _ T.bankEq (program map (@Admitted.source _ _ S.bankEq p)) facts with
      | error reason =>
        rw [ran] at ok
        cases ok
      | ok accepted =>
        rw [ran] at ok
        cases Except.ok.inj ok
        exact ⟨(checkWrites_iff _ _).mp safe, facts, rfl, ran⟩
  · simp [replay, safe] at ok

private theorem compile_ok (map : PortMap S T) (p : AdmittedAt S result) (target : Generated T result)
    (ok : compile map p = .ok target) : replay map p = .ok target.source := by
  unfold compile at ok
  cases ran : replay map p with
  | error reason =>
    rw [ran] at ok
    cases ok
  | ok accepted =>
    rw [ran] at ok
    cases Except.ok.inj ok
    rfl

theorem compile_safe (map : PortMap S T) (p : AdmittedAt S result) (target : Generated T result)
    (ok : compile map p = .ok target) : SafeWrites map (@Admitted.source _ _ S.bankEq p) :=
  (replay_ok map p target.source (compile_ok map p target ok)).1

theorem compile_admit (map : PortMap S T) (p : AdmittedAt S result) (target : Generated T result)
    (ok : compile map p = .ok target) :
    @admit _ _ T.bankEq (program map (@Admitted.source _ _ S.bankEq p))
      (@Admitted.facts _ _ T.bankEq target.source) = .ok target.source := by
  obtain ⟨_, facts, _, admitted⟩ := replay_ok map p target.source (compile_ok map p target ok)
  rw [(admit_fields _ facts _ admitted).2]
  exact admitted

theorem compile_source (map : PortMap S T) (p : AdmittedAt S result) (target : Generated T result)
    (ok : compile map p = .ok target) :
    @Admitted.source _ _ T.bankEq target.source = program map (@Admitted.source _ _ S.bankEq p) :=
  (admit_fields _ _ _ (compile_admit map p target ok)).1

theorem compile_facts (map : PortMap S T) (p : AdmittedAt S result) (target : Generated T result)
    (ok : compile map p = .ok target) :
    pushFacts map (@Admitted.facts _ _ S.bankEq p) = some (@Admitted.facts _ _ T.bankEq target.source) := by
  obtain ⟨_, facts, pushed, admitted⟩ := replay_ok map p target.source (compile_ok map p target ok)
  rw [(admit_fields _ facts _ admitted).2]
  exact pushed

theorem compile_coverage (map : PortMap S T) (p : AdmittedAt S result) (target : Generated T result)
    (ok : compile map p = .ok target) (input : Valuation T) :
    TupleCovers (@Admitted.facts _ _ T.bankEq target.source) input ↔
      TupleCovers (@Admitted.facts _ _ S.bankEq p) (reduct map input) := by
  exact pushFacts_covers map _ _ (compile_facts map p target ok) input

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Proofs
