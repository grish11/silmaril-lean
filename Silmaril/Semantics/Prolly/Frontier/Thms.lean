module

public import Silmaril.Semantics.Prolly.Frontier.Defs
import Silmaril.Proofs.Semantics.Prolly.Frontier

public section

namespace Silmaril.Semantics.Prolly

variable {Key Payload Name Item : Type}

theorem keyStep_length_le (policy : Policy Key) (level : Nat) (keys : List Key) :
    (keyStep policy level keys).length ≤ (chunk (policy.cut level) keys).length :=
  List.length_filterMap_le _ _

theorem lift_chunk_keys (policy : Policy Key) (level : Nat) (items : List (Key × Item)) :
    (lift (chunk (fun count pair => policy.cut level count pair.1) items)).map Prod.fst =
      keyStep policy level (items.map Prod.fst) :=
  Proofs.Semantics.Prolly.Frontier.lift_chunk_keys policy level items

/-- The builder's root level counts actual promotions, not allotted fuel. -/
theorem build_level_eq_promotions [LinearOrder Key] (policy : Policy Key) (map : OrderedMap Key Payload) :
    (build policy map).level = (promotions policy map.entries.length 0 (map.entries.map Prod.fst)).length := by
  simpa [build] using Proofs.Semantics.Prolly.Frontier.grow_level policy map.entries.length 0 map.entries

/-- Counts unfolded block occurrences, not distinct names or encoded bytes. A
root-only tree has one block, including when its input map is empty. -/
theorem build_occurrences_eq_promotions [LinearOrder Key] (policy : Policy Key)
    (map : OrderedMap Key Payload) (address : Block Name Key Payload → Name) :
    (blockOccurrences address (build policy map).level (build policy map).root).length =
      1 + ((promotions policy map.entries.length 0 (map.entries.map Prod.fst)).map List.length).sum := by
  simpa [build, blockOccurrences] using
    Proofs.Semantics.Prolly.Frontier.grow_occurrences policy address map.entries.length 0 map.entries

end Silmaril.Semantics.Prolly
