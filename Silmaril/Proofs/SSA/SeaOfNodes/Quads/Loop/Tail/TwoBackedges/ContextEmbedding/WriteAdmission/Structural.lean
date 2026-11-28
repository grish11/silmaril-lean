module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.WriteAdmission.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.WriteAdmission.Diagnostic
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Thms

/-! Split the second structural check into collisions inside and outside the first image. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.WriteAdmission.Proofs

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Loop.MLIR.CF (Op)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Port)
open Identification (BankMap PortMap SafeWrites checkWrites quad quads program)
open Composition (thenMap)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted)
open Reindex.Guarded.Institution (AdmittedAt Generated)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {old middle new : List (ValueSort Width)} {out : ValueSort Width}
variable {S T U : EntrySignature} {result : Width}

private theorem quads_program (first : BankMap old middle) (p : Program Op old out) :
    quads (program first p) = (quads p).map (quad first) := by
  simp only [quads, program, List.map_append]

private theorem no_alias_at (first : BankMap old middle) (second : BankMap middle new)
    (p : Program Op middle out) (absent : diagnose first second p = none)
    (q : Quad Op middle) (present : q ∈ quads p)
    (other : Port (dataPorts middle) (.value q.result)) : ¬ OutsideAlias first second q.dest other := by
  obtain ⟨occurrence, rfl⟩ := List.mem_iff_get.mp present
  exact (diagnose_none_iff first second p).mp absent ⟨occurrence, other⟩

private theorem second_safe (first : BankMap old middle) (second : BankMap middle new) (p : Program Op old out)
    (direct : SafeWrites (thenMap first second) p) (absent : diagnose first second (program first p) = none) :
    SafeWrites second (program first p) := by
  intro q present sort other shared
  have inProgram := present
  rw [quads_program] at present
  obtain ⟨writer, written, rfl⟩ := List.mem_map.mp present
  obtain ⟨rfl, imageEq⟩ := Sigma.mk.inj_iff.mp (Reindex.slot_eq _ _ shared)
  have sameTarget := eq_of_heq imageEq
  by_cases represented : ∃ source, first _ source = other
  · obtain ⟨source, samePort⟩ := represented
    have oldShared : slot ((thenMap first second) _ source) = slot ((thenMap first second) _ writer.dest) := by
      change slot (second _ (first _ source)) = slot (second _ (first _ writer.dest))
      rw [samePort, sameTarget]
      rfl
    have sameOld := eq_of_heq (Sigma.mk.inj_iff.mp
      (Reindex.slot_eq _ _ (direct writer written _ source oldShared))).2
    rw [← samePort, sameOld]
    rfl
  · by_contra apart
    exact no_alias_at first second (program first p) absent _ inProgram other ⟨apart, sameTarget, represented⟩

theorem staged_checks_eq (first : BankMap old middle) (second : BankMap middle new) (p : Program Op old out) :
    (checkWrites first p && checkWrites second (program first p)) =
      (checkWrites (thenMap first second) p && (diagnose first second (program first p)).isNone) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, Identification.checkWrites_iff, Option.isNone_iff_eq_none]
  constructor
  · rintro ⟨safeFirst, safeSecond⟩
    refine ⟨Composition.safeWrites_thenMap first second p safeFirst safeSecond, ?_⟩
    apply (diagnose_none_iff first second (program first p)).mpr
    intro c collision
    exact collision.1 (safeSecond _ (List.get_mem _ c.occurrence) _ c.other (congrArg slot collision.2.1))
  · rintro ⟨safeDirect, absent⟩
    exact ⟨Composition.safeWrites_of_thenMap first second p safeDirect, second_safe first second p safeDirect absent⟩

theorem checked_second_eq (first : PortMap S T) (second : PortMap T U) (p : AdmittedAt S result)
    (mid : Generated T result) (firstOk : Identification.compile first p = .ok mid) :
    checkWrites second (@Admitted.source _ _ T.bankEq mid.source) =
      (checkWrites (thenMap first second) (@Admitted.source _ _ S.bankEq p) &&
        (diagnose first second (@Admitted.source _ _ T.bankEq mid.source)).isNone) := by
  have checked := (Identification.checkWrites_iff _ _).mpr (Identification.compile_safe first p firstOk)
  rw [Identification.compile_source first p firstOk]
  simpa only [checked, Bool.true_and] using staged_checks_eq first second (@Admitted.source _ _ S.bankEq p)

theorem compile_by_diagnosis (first : PortMap S T) (second : PortMap T U) (p : AdmittedAt S result)
    (mid : Generated T result) (firstOk : Identification.compile first p = .ok mid) :
    Identification.compile second mid.source =
      match diagnose first second (@Admitted.source _ _ T.bankEq mid.source) with
      | none => Identification.compile (thenMap first second) p
      | some _ => .error .aliasedWrite := by
  rw [FactTransport.second_compile_check first second p mid firstOk, checked_second_eq first second p mid firstOk]
  cases diagnose first second (@Admitted.source _ _ T.bankEq mid.source) with
  | none =>
    cases checked : checkWrites (thenMap first second) (@Admitted.source _ _ S.bankEq p)
    · simp [Identification.compile, Identification.replay, checked, Except.map]
    · rfl
  | some _ => simp

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.WriteAdmission.Proofs
