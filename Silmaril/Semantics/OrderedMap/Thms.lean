module

public import Silmaril.Semantics.OrderedMap.Defs
import Silmaril.Proofs.Semantics.OrderedMap.Basic

public section

namespace Silmaril.Semantics.OrderedMap

variable {Key Payload : Type} [LinearOrder Key]

@[simp] theorem ofEntries?_entries (map : OrderedMap Key Payload) : ofEntries? map.entries = some map := by
  cases map with
  | mk entries ordered => simp [ofEntries?, ordered]

theorem keys_nodup (map : OrderedMap Key Payload) : map.keys.Nodup :=
  List.nodup_iff_pairwise_ne.mpr (List.pairwise_map.mpr (map.ordered.imp ne_of_lt))

theorem lookup_eq_some_iff (map : OrderedMap Key Payload) {key : Key} {value : Payload} :
    map.lookup? key = some value ↔ (key, value) ∈ map.entries :=
  Proofs.Semantics.OrderedMap.lookup_entries_iff map.entries map.ordered key value

theorem eq_of_lookup {left right : OrderedMap Key Payload} (same : ∀ key, left.lookup? key = right.lookup? key) :
    left = right := Proofs.Semantics.OrderedMap.entries_ext (fun (key, _) => by
  rw [← left.lookup_eq_some_iff, ← right.lookup_eq_some_iff, same key])

end Silmaril.Semantics.OrderedMap
