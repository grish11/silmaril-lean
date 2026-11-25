module

public import Silmaril.Semantics.Operational.Environment.Finite.Defs
import Silmaril.Proofs.Semantics.Operational.Environment.Finite

public section

namespace Silmaril.Semantics.Operational.Environment.Finite

variable {Key Value : Type*} [DecidableEq Key]

theorem view_empty : view (∅ : AList (fun _ : Key => Value)) = Environment.empty :=
  rfl

theorem view_insert (rows : AList (fun _ : Key => Value)) (key : Key) (value : Value) :
    view (rows.insert key value) = Environment.set (view rows) key value := by
  funext other
  rcases eq_or_ne other key with rfl | different <;> simp_all [view]

theorem view_erase (rows : AList (fun _ : Key => Value)) (key : Key) :
    view (rows.erase key) = Environment.erase (view rows) key := by
  funext other
  rcases eq_or_ne other key with rfl | different <;> simp_all [view]

theorem mem_entries_iff {rows : AList (fun _ : Key => Value)} {key : Key} {value : Value} :
    Sigma.mk key value ∈ rows.entries ↔ view rows key = some value :=
  AList.mem_lookup_iff.symm

theorem view_supported (rows : AList (fun _ : Key => Value)) :
    Environment.SupportedBy (view rows) rows.keys := by
  intro key value present
  exact List.mem_keys_of_mem (mem_entries_iff.mpr present)

/-- Two valid finite layouts have the same view exactly when their rows
are permutations. The projected map does not recover their order. -/
theorem view_eq_iff_perm (left right : AList (fun _ : Key => Value)) :
    view left = view right ↔ List.Perm left.entries right.entries :=
  Proofs.Semantics.Operational.Environment.Finite.view_eq_iff_perm left right

theorem view_encode_apply (env : Environment Key Value) (keys : List Key) (key : Key) :
    view (encode env keys) key = if key ∈ keys then env key else none :=
  Proofs.Semantics.Operational.Environment.Finite.view_encode_apply env keys key

theorem view_encode {env : Environment Key Value} {keys : List Key}
    (supported : Environment.SupportedBy env keys) : view (encode env keys) = env := by
  funext key
  by_cases present : key ∈ keys <;>
    simp [view_encode_apply, present, Environment.absent_outside_support env keys supported]

end Silmaril.Semantics.Operational.Environment.Finite
