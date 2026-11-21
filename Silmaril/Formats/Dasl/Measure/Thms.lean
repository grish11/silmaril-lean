module

public import Mathlib.Data.Finset.Card
public import Silmaril.Formats.Dasl.Measure.Defs
public import Silmaril.Formats.Dasl.Resolve.Thms
import Silmaril.Proofs.Formats.Dasl.Measure

public section

namespace Silmaril.Formats.Dasl

variable {Name Ref : Type}

theorem Tree.measure_valid (scope : Scope) (tree : Tree Ref Name) : (tree.measure scope).Valid :=
  Proofs.Formats.Dasl.Measure.measure_valid scope tree

theorem Partial.mem_blockOccurrences_iff (tree : Partial Name) (block : Block Name) :
    block ∈ tree.blockOccurrences ↔ block.BoundIn tree.bindings :=
  Proofs.Formats.Dasl.Measure.mem_occurrences_iff tree block

theorem PartialNames.blocks_bound {store : Store Name} {root : Name} {tree : Partial Name}
    (present : PartialNames store root tree) {block : Block Name} (hit : block ∈ tree.blocks root) :
    block.BoundIn store := Proofs.Formats.Dasl.Measure.blocks_bound present hit

theorem FullNames.blocks_bound {store : Store Name} {root : Name} {tree : Named Name}
    (present : FullNames store root tree) {block : Block Name} (hit : block ∈ tree.blocks root) :
    block.BoundIn store := present.toPartial.blocks_bound hit

theorem Block.eq_of_same_link {store : Store Name} (bound : store.Binding) {left right : Block Name}
    (first : left.BoundIn store) (second : right.BoundIn store) (same : left.link = right.link) : left = right :=
  Proofs.Formats.Dasl.Measure.block_eq_of_same_link bound first second same

theorem inline_within_max {blocks : List (Block Name)} {block : Block Name} (hit : block ∈ blocks) :
    block.inlineMetrics.Within (maxInlineMetrics blocks) := Proofs.Formats.Dasl.Measure.inline_within_max hit

theorem bytes_within_max {serialize : Shallow Name → Option ByteArray} {blocks : List (Block Name)}
    {block : Block Name} (hit : block ∈ blocks) {limit : Nat} (checked : maxBlockBytes? serialize blocks = some limit) :
    ∃ bytes, block.byteSize? serialize = some bytes ∧ bytes ≤ limit :=
  Proofs.Formats.Dasl.Measure.bytes_within_max hit checked

theorem distinct_count_le_occurrences [DecidableEq Name] (blocks : List (Block Name)) :
    (distinctLinks blocks).card ≤ blocks.length := by
  simpa only [distinctLinks, List.length_map] using (List.toFinset_card_le (l := blocks.map Block.link))

open Silmaril.Semantics.Naming in
theorem storeByteSize_agrees {store : Store Name} (bound : store.Binding) (serialize : Shallow Name → Option ByteArray) :
    byteSizeAgrees store serialize (storeByteSize? bound serialize) := by
  intro block hit
  cases block with
  | object name value => simp [storeByteSize?, Block.link, Block.byteSize?, (bound.1.lookup_eq_some).mpr hit]
  | blob name bytes => simp [storeByteSize?, Block.link, Block.byteSize?, (bound.2.lookup_eq_some).mpr hit]

end Silmaril.Formats.Dasl
