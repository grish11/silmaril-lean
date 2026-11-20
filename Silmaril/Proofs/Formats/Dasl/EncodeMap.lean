module

public import Silmaril.Formats.Dasl.Encode.Map.Defs
public import Silmaril.Semantics.OrderedMap.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl.EncodeMap

open Silmaril.Semantics

theorem keys_roundtrip {Key : Type} [LinearOrder Key] (set : OrderedSet Key) :
    OrderedSet.ofKeys? set.keys = some set := by
  have same : (set.entries.map Prod.fst).map (·, ()) = set.entries := by
    rw [List.map_map]
    exact (List.map_congr_left (g := id) (fun ⟨_, ()⟩ _ => rfl)).trans (List.map_id _)
  unfold OrderedSet.ofKeys? OrderedMap.keys
  rw [same, OrderedMap.ofEntries?_entries]

end Silmaril.Proofs.Formats.Dasl.EncodeMap
