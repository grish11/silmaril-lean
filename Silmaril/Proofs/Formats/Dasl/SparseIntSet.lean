module

public import Silmaril.Formats.Dasl.SparseIntSet.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl.SparseIntSet

open Silmaril.Formats.Dasl.SparseIntSet Silmaril.Semantics

attribute [local instance] signedOrder

theorem ofFinset_members (layout : Layout) : ofFinset (members layout) = layout := by
  have sorted : layout.keys.Pairwise signedOrder.le := List.pairwise_map.mpr (layout.ordered.imp le_of_lt)
  have recovered : (members layout).sort signedOrder.le = layout.keys :=
    (List.toFinset_sort signedOrder.le layout.keys_nodup).mpr sorted
  apply OrderedMap.ext
  change ((members layout).sort signedOrder.le).map (·, ()) = layout.entries
  rw [recovered]
  simp [OrderedMap.keys, List.map_map, Function.comp_def]

end Silmaril.Proofs.Formats.Dasl.SparseIntSet
