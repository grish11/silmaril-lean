module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.WriteAdmission.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.WriteAdmission.Diagnostic
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.WriteAdmission.Structural

/-! Exact structural and compiler laws for the extra intermediate check. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.WriteAdmission

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op)
open Silmaril.MLIR.Arith (Width)
open Identification (BankMap PortMap checkWrites program)
open Composition (thenMap)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted)
open Reindex.Guarded.Institution (AdmittedAt Generated)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {old middle new : List (ValueSort Width)} {out : ValueSort Width}
variable {S T U : EntrySignature} {result : Width}

theorem diagnose_sound (first : BankMap old middle) (second : BankMap middle new)
    {p : Program Op middle out} {collision : Conflict p}
    (found : diagnose first second p = some collision) : collision.Valid first second :=
  Proofs.diagnose_sound first second found

theorem diagnose_isSome (first : BankMap old middle) (second : BankMap middle new) (p : Program Op middle out) :
    (diagnose first second p).isSome ↔ ∃ c : Conflict p, c.Valid first second :=
  Proofs.diagnose_isSome first second p

theorem diagnose_none_iff (first : BankMap old middle) (second : BankMap middle new) (p : Program Op middle out) :
    diagnose first second p = none ↔ ∀ c : Conflict p, ¬ c.Valid first second :=
  Proofs.diagnose_none_iff first second p

/-- Both staged write checks pass exactly when the composite passes and
there is no alias through an intermediate port outside the first image. -/
theorem staged_checks_eq (first : BankMap old middle) (second : BankMap middle new) (p : Program Op old out) :
    (checkWrites first p && checkWrites second (program first p)) =
      (checkWrites (thenMap first second) p && (diagnose first second (program first p)).isNone) :=
  Proofs.staged_checks_eq first second p

/-- Use the actual intermediate program emitted by a successful first call. -/
theorem checked_second_eq (first : PortMap S T) (second : PortMap T U) (p : AdmittedAt S result)
    (mid : Generated T result) (firstOk : Identification.compile first p = .ok mid) :
    checkWrites second (@Admitted.source _ _ T.bankEq mid.source) =
      (checkWrites (thenMap first second) (@Admitted.source _ _ S.bankEq p) &&
        (diagnose first second (@Admitted.source _ _ T.bankEq mid.source)).isNone) :=
  Proofs.checked_second_eq first second p mid firstOk

theorem second_passes_iff (first : PortMap S T) (second : PortMap T U) (p : AdmittedAt S result)
    (mid : Generated T result) (firstOk : Identification.compile first p = .ok mid)
    (directSafe : checkWrites (thenMap first second) (@Admitted.source _ _ S.bankEq p) = true) :
    checkWrites second (@Admitted.source _ _ T.bankEq mid.source) = true ↔
      diagnose first second (@Admitted.source _ _ T.bankEq mid.source) = none := by
  rw [checked_second_eq first second p mid firstOk, directSafe, Bool.true_and]
  exact Option.isNone_iff_eq_none

/-- After first admission, an absent diagnostic gives the identical final
compiler result. A reported collision gives the actual second write refusal. -/
theorem compile_by_diagnosis (first : PortMap S T) (second : PortMap T U) (p : AdmittedAt S result)
    (mid : Generated T result) (firstOk : Identification.compile first p = .ok mid) :
    Identification.compile second mid.source =
      match diagnose first second (@Admitted.source _ _ T.bankEq mid.source) with
      | none => Identification.compile (thenMap first second) p
      | some _ => .error .aliasedWrite :=
  Proofs.compile_by_diagnosis first second p mid firstOk

theorem compile_eq_of_none (first : PortMap S T) (second : PortMap T U) (p : AdmittedAt S result)
    (mid : Generated T result) (firstOk : Identification.compile first p = .ok mid)
    (absent : diagnose first second (@Admitted.source _ _ T.bankEq mid.source) = none) :
    Identification.compile second mid.source = Identification.compile (thenMap first second) p := by
  rw [compile_by_diagnosis first second p mid firstOk, absent]

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.WriteAdmission
