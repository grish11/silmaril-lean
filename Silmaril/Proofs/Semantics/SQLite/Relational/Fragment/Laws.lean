module

public import Silmaril.Semantics.SQLite.Relational.Fragment.Defs
public import Silmaril.Semantics.Relational.UB.QueryThms

public section

namespace Silmaril.Proofs.Semantics.SQLite.Relational.Fragment

open Silmaril.SQLite.Relational
open Silmaril.Relational (QueryRel)
open Silmaril.Relational.UB (ExplicitQuery CatastrophicQuery)

variable {p : Profile}

theorem check_eq (exec : Executor p) :
    QueryRel.ofTotal exec.check = CheckedRequest.denote exec.denote := by
  funext db request out
  cases request with
  | invoke call =>
    apply propext
    constructor
    · intro eq
      exact ⟨exec.execute db call, rfl, eq⟩
    · rintro ⟨result, observed, view⟩
      change exec.execute db call = result at observed
      subst result
      exact view
  | unsupported _ => rfl

theorem checked_refines
    {impl spec : QueryRel (Connection p) (Invocation p.Ref) (Outcome p)}
    (h : impl.Refines spec) : (CheckedRequest.denote impl).Refines (CheckedRequest.denote spec) := by
  intro db request out seen
  cases request with
  | invoke call => exact (h.observe CheckedOutcome.ofStatement) seen
  | unsupported _ => exact seen

theorem explicit_refines {impl spec : QueryRel (Connection p) (Invocation p.Ref) (Outcome p)}
    (h : impl.Refines spec) : HostRequest.explicit impl ≤ HostRequest.explicit spec := by
  apply (ExplicitQuery.le_extendUB_iff _ _ _ _).mpr
  refine ⟨?_, ?_⟩
  · rw [HostRequest.explicit, ExplicitQuery.restrict_extendUB]
    exact fun _ _ => ⟨fun _ seen => checked_refines h seen, le_rfl⟩
  · intro db request outside
    rw [HostRequest.explicit, ExplicitQuery.extendUB_apply_outside _ _ _ _ _ outside]

theorem collapse_explicit (sem : QueryRel (Connection p) (Invocation p.Ref) (Outcome p)) :
    (HostRequest.explicit sem).collapse = HostRequest.catastrophic sem := by
  rw [HostRequest.explicit, HostRequest.catastrophic, ExplicitQuery.collapse_extendUB]
  congr 1
  funext db checked
  exact Silmaril.Relational.UB.Explicit.collapse_defined _

end Silmaril.Proofs.Semantics.SQLite.Relational.Fragment
