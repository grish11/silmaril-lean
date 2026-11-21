module

public import Silmaril.Semantics.OrderedMap.Defs

public section

namespace Silmaril.Proofs.Semantics.OrderedMap

open Silmaril.Semantics

variable {Key Payload : Type} [LinearOrder Key]

theorem lookup_entries_iff (entries : List (Key × Payload))
    (ordered : entries.Pairwise (fun left right => left.1 < right.1)) (key : Key) (value : Payload) :
    entries.lookup key = some value ↔ (key, value) ∈ entries := by
  induction entries with
  | nil => simp
  | cons entry tail ih =>
    obtain ⟨head, payload⟩ := entry
    have ⟨lower, tailOrder⟩ := List.pairwise_cons.mp ordered
    by_cases same : key = head
    · subst head
      have missing : (key, value) ∉ tail := fun hit => (lt_irrefl key) (lower _ hit)
      simp [missing, eq_comm]
    · have unequal : (key == head) = false := beq_eq_false_iff_ne.mpr same
      simpa [List.lookup_cons, unequal, same] using ih tailOrder

theorem entries_ext {left right : Silmaril.Semantics.OrderedMap Key Payload}
    (same : ∀ entry, entry ∈ left.entries ↔ entry ∈ right.entries) : left = right := by
  have nodup (map : Silmaril.Semantics.OrderedMap Key Payload) : map.entries.Nodup :=
    List.nodup_iff_pairwise_ne.mpr (map.ordered.imp (S := fun left right => left ≠ right)
      fun lt equal => (lt_irrefl _) (equal ▸ lt))
  have perm := (List.perm_ext_iff_of_nodup (nodup left) (nodup right)).mpr same
  exact Silmaril.Semantics.OrderedMap.ext (List.Perm.eq_of_pairwise
    (fun _ _ _ _ first second => (lt_asymm first second).elim) left.ordered right.ordered perm)

end Silmaril.Proofs.Semantics.OrderedMap
