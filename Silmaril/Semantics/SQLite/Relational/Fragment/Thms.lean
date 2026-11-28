module

public import Silmaril.Semantics.SQLite.Relational.Fragment.Defs
public import Silmaril.Semantics.SQLite.Relational.Executor.Thms
public import Silmaril.Semantics.Relational.UB.QueryThms
import Silmaril.Proofs.Semantics.SQLite.Relational.Fragment.Laws

public section

namespace Silmaril.SQLite.Relational

open Silmaril.Relational (QueryRel)
open Silmaril.Relational.UB (Explicit ExplicitQuery CatastrophicQuery)

variable {p : Profile}

theorem Executor.check_eq (exec : Executor p) :
    QueryRel.ofTotal exec.check = CheckedRequest.denote exec.denote :=
  Proofs.Semantics.SQLite.Relational.Fragment.check_eq exec

theorem CheckedRequest.restrict_invocation
    (sem : QueryRel (Connection p) (Invocation p.Ref) (Outcome p)) :
    (CheckedRequest.denote sem).restrict (invocationEmbedding p.Ref) =
      sem.observe CheckedOutcome.ofStatement := rfl

/-- The ordinary out-of-scope response is a defined singleton. -/
theorem CheckedRequest.unsupported_iff
    (sem : QueryRel (Connection p) (Invocation p.Ref) (Outcome p))
    (db : Connection p) (feature : String) (out : CheckedOutcome p) :
    CheckedRequest.denote sem db (.unsupported feature) out ↔
      (.unsupported feature, db) = out := Iff.rfl

namespace HostRequest

variable (sem : QueryRel (Connection p) (Invocation p.Ref) (Outcome p))

theorem restrict_explicit :
    (explicit sem).restrict (checkedEmbedding p.Ref) =
      ExplicitQuery.ofQueryRel (CheckedRequest.denote sem) :=
  ExplicitQuery.restrict_extendUB _ _ _

theorem restrict_catastrophic :
    (catastrophic sem).restrict (checkedEmbedding p.Ref) =
      CatastrophicQuery.ofQueryRel (CheckedRequest.denote sem) :=
  CatastrophicQuery.restrict_extendUB _ _

/-- Both defined statement errors and scope rejections have empty reason sets. -/
theorem checked_explicit (db : Connection p) (request : CheckedRequest p.Ref) :
    explicit sem db (.checked request) =
      Explicit.defined ((CheckedRequest.denote sem).toNondet db request) := by
  change (explicit sem).restrict (checkedEmbedding p.Ref) db request = _
  rw [restrict_explicit]
  rfl

theorem finalized_explicit (db : Connection p) :
    explicit sem db .bindFinalized = Explicit.undefined .bindFinalized :=
  ExplicitQuery.extendUB_apply_outside _ _ _ _ _ (by rintro ⟨_, h⟩; cases h)

theorem finalized_catastrophic (db : Connection p) :
    catastrophic sem db .bindFinalized = ⊤ :=
  CatastrophicQuery.extendUB_apply_outside _ _ _ _ (by rintro ⟨_, h⟩; cases h)

theorem collapse_explicit : (explicit sem).collapse = catastrophic sem :=
  Proofs.Semantics.SQLite.Relational.Fragment.collapse_explicit sem

theorem explicit_refines {impl spec : QueryRel (Connection p) (Invocation p.Ref) (Outcome p)}
    (h : impl.Refines spec) : explicit impl ≤ explicit spec :=
  Proofs.Semantics.SQLite.Relational.Fragment.explicit_refines h

theorem catastrophic_refines {impl spec : QueryRel (Connection p) (Invocation p.Ref) (Outcome p)}
    (h : impl.Refines spec) : catastrophic impl ≤ catastrophic spec := by
  rw [← collapse_explicit impl, ← collapse_explicit spec]
  exact ExplicitQuery.collapse_mono (explicit_refines h)

end HostRequest
end Silmaril.SQLite.Relational
