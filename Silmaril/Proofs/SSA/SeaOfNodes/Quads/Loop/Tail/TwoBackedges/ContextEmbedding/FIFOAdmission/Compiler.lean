module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Refinement
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Worklist.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.Thms

/-! A write-safe suffix cannot recover a first-stage FIFO refusal. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Proofs

open SeaOfNodes.Loop.MLIR.CF (Op model)
open Silmaril.MLIR.Arith (Width)
open Composition (thenMap)
open Identification (PortMap checkWrites program pushFacts)
open SCCP (incomingIndex)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted EntryFacts admit)
open Reindex.Guarded.Institution (AdmittedAt)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {S T U : EntrySignature} {result : Width}

theorem admit_refusal_iff (code : Program Op T.regs (.data result)) (facts : EntryFacts T.regs)
    (reason : SCCP.Dispatch.Refusal) :
    @admit _ _ T.bankEq code facts = .error reason ↔
      Refuses (@SCCP.Worklist.solve _ _ _ _ model code T.bankEq facts).1 reason := by
  let _ := T.bankEq
  rw [SCCP.Worklist.solve_eq_simultaneous]
  have erased :
      @admit _ _ T.bankEq code facts = .error reason ↔ SCCP.Dispatch.admit model code facts = .error reason := by
    rw [← SCCP.Dispatch.DeleteRoute.Bypass.Backends.Worklist.admit_eq_simultaneous]
    dsimp only [admit]
    split <;> simp_all
  rw [erased]
  cases reason with
  | bothMarked => exact SCCP.Dispatch.admit_bothMarked_iff
  | neitherMarked => exact SCCP.Dispatch.admit_neitherMarked_iff

theorem compile_checker_iff (map : PortMap S T) (seed : AdmittedAt S result)
    (reason : SCCP.Dispatch.Refusal) : Identification.compile map seed = .error (.checker reason) ↔
    checkWrites map (@Admitted.source _ _ S.bankEq seed) = true ∧
      ∃ facts, pushFacts map (@Admitted.facts _ _ S.bankEq seed) = some facts ∧
        Refuses (@SCCP.Worklist.solve _ _ _ _ model
          (program map (@Admitted.source _ _ S.bankEq seed)) T.bankEq facts).1 reason := by
  by_cases writes : checkWrites map (@Admitted.source _ _ S.bankEq seed) = true
  · cases pushed : pushFacts map (@Admitted.facts _ _ S.bankEq seed) with
    | none => simp [Identification.compile, Identification.replay, writes, pushed, Except.map]
    | some facts =>
      simp only [Identification.compile, Identification.replay, writes, ite_true, pushed, true_and,
        Option.some.injEq, exists_eq_left']
      rw [← admit_refusal_iff]
      cases checked : @admit _ _ T.bankEq (program map (@Admitted.source _ _ S.bankEq seed)) facts
      <;> simp [Except.map, Identification.Refusal.checker.injEq]
  · simp [Identification.compile, Identification.replay, writes, Except.map]

theorem compile_never_both (map : PortMap S T) (seed : AdmittedAt S result) :
    Identification.compile map seed ≠ .error (.checker .bothMarked) := by
  let _ := S.bankEq
  intro failed
  obtain ⟨writes, facts, pushed, both⟩ := (compile_checker_iff map seed .bothMarked).mp failed
  have smaller := fifo_marks_subset map _ ((Identification.checkWrites_iff _ _).mp writes)
    _ facts (FactTransport.pushFacts_refines _ _ _ pushed)
  have marked : incomingIndex (.feedback !seed.checked.side) ∈
      (@SCCP.Worklist.solve _ _ _ _ model (program map (@Admitted.source _ _ S.bankEq seed)) T.bankEq facts).1 := by
    cases seed.checked.side
    · exact both.1
    · exact both.2
  have impossible := smaller marked
  rw [SCCP.Worklist.solve_eq_simultaneous] at impossible
  exact seed.checked.excluded impossible

theorem direct_of_neither (first : PortMap S T) (second : PortMap T U) (seed : AdmittedAt S result)
    (refused : Identification.compile first seed = .error (.checker .neitherMarked))
    (writeSafe : checkWrites second (program first (@Admitted.source _ _ S.bankEq seed)) = true) :
    Identification.compile (thenMap first second) seed =
      match pushFacts (thenMap first second) (@Admitted.facts _ _ S.bankEq seed) with
      | none => .error .incompatibleFacts
      | some _ => .error (.checker .neitherMarked) := by
  obtain ⟨firstSafe, mid, pushed, neither⟩ := (compile_checker_iff first seed .neitherMarked).mp refused
  have safe := (Identification.checkWrites_iff _ _).mp writeSafe
  have directSafe := (Identification.checkWrites_iff _ _).mpr
    (Composition.safeWrites_thenMap first second _ ((Identification.checkWrites_iff _ _).mp firstSafe) safe)
  have factEq := FactTransport.pushFacts_comp first second (@Admitted.facts _ _ S.bankEq seed)
  rw [pushed] at factEq
  change pushFacts (thenMap first second) (@Admitted.facts _ _ S.bankEq seed) = pushFacts second mid at factEq
  rw [factEq]
  cases final : pushFacts second mid with
  | none =>
    simp [Identification.compile, Identification.replay, directSafe, factEq, final, Except.map]
  | some facts =>
    apply (compile_checker_iff (thenMap first second) seed .neitherMarked).mpr
    refine ⟨directSafe, facts, factEq.trans final, ?_⟩
    rw [← Composition.program_thenMap]
    have smaller := fifo_marks_subset second _ safe mid facts (FactTransport.pushFacts_refines _ _ _ final)
    exact ⟨fun yes => neither.1 (smaller yes), fun no => neither.2 (smaller no)⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Proofs
