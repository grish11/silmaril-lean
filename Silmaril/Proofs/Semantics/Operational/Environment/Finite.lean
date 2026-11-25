module

public import Silmaril.Semantics.Operational.Environment.Finite.Defs

public section

namespace Silmaril.Proofs.Semantics.Operational.Environment.Finite

open Silmaril.Semantics.Operational.Environment.Finite
open Silmaril.Semantics.Operational

variable {Key Value : Type*} [DecidableEq Key]

theorem view_encode_apply (env : Environment Key Value) (keys : List Key) (key : Key) :
    view (encode env keys) key = if key ∈ keys then env key else none := by
  induction keys with
  | nil => rfl
  | cons head tail ih =>
    by_cases same : key = head
    · subst head
      cases found : env key with
      | none => simp [encode, found, ih]
      | some value => simp [encode, found, view]
    · cases found : env head with
      | none => simp [encode, found, ih, same]
      | some value =>
        rw [encode, found]
        change ((encode env tail).insert head value).lookup key = _
        rw [AList.lookup_insert_ne same]
        exact ih.trans (by simp [same])

theorem view_eq_iff_perm (left right : AList (fun _ : Key => Value)) :
    view left = view right ↔ List.Perm left.entries right.entries := by
  constructor
  · intro same
    apply List.lookup_ext left.nodupKeys right.nodupKeys
    intro key value
    change value ∈ view left key ↔ value ∈ view right key
    rw [same]
  · exact fun perm => funext (fun key => AList.perm_lookup (a := key) perm)

end Silmaril.Proofs.Semantics.Operational.Environment.Finite
