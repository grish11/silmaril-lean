module

public import Silmaril.Formats.Dasl.Mst.Route.Defs
import Silmaril.Proofs.Formats.Dasl.MstRouteComplete

public section

namespace Silmaril.Proofs.Formats.Dasl.MstRooted

open Silmaril.Formats.Dasl.Mst Silmaril.Semantics.Naming

variable {Name : Type}

private theorem record_slot (entries : List (Entry Name)) (ctx : Context) (left : Option Name)
    (entry : Entry Name) (present : entry ∈ entries) : Slot.record entry.key entry.record ∈ slotsFrom ctx left entries := by
  induction entries generalizing ctx left with
  | nil => cases present
  | cons first rest ih =>
    rcases List.mem_cons.mp present with rfl | later
    · simp [slotsFrom]
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih _ _ later))

private theorem slot_record (entries : List (Entry Name)) (ctx : Context) (left : Option Name)
    {key : Key} {record : Name} (hit : Slot.record key record ∈ slotsFrom ctx left entries) :
    ∃ entry ∈ entries, entry.key = key ∧ entry.record = record := by
  induction entries generalizing ctx left with
  | nil => simp [slotsFrom] at hit
  | cons first rest ih =>
    rcases List.mem_cons.mp hit with impossible | later
    · cases impossible
    · rcases List.mem_cons.mp later with same | later
      · obtain ⟨rfl, rfl⟩ := Slot.record.inj same
        exact ⟨first, by simp, rfl, rfl⟩
      · obtain ⟨entry, present, same⟩ := ih _ _ later
        exact ⟨entry, List.mem_cons_of_mem _ present, same⟩

private theorem group_record {node : Node Name} {ctx : Context} {groups : List (SlotEntries Name)}
    (slots : groups.map Prod.fst = node.slots ctx)
    (records : ∀ group ∈ groups, ∀ key record, group.1 = .record key record → group.2 = [(key, record)])
    (entry : Entry Name) (present : entry ∈ node.entries) : (entry.key, entry.record) ∈ groups.flatMap Prod.snd := by
  have slot := record_slot node.entries {ctx with layer := ctx.layer - 1, root := false} node.left entry present
  change Slot.record entry.key entry.record ∈ node.slots ctx at slot
  rw [← slots] at slot
  obtain ⟨group, inGroups, same⟩ := List.mem_map.mp slot
  exact List.mem_flatMap.mpr ⟨group, inGroups, by rw [records group inGroups _ _ same]; simp⟩

theorem layers {layerOf : Key → Nat} {reference : Relation Name (Node Name)}
    {expected : Option Context} {name : Name} {entries : List (Key × Name)}
    (tree : Realizes layerOf reference expected name entries) :
    ∃ node, reference name node ∧
      (∀ pair ∈ entries, layerOf pair.1 ≤ (expected.getD (node.rootContext layerOf)).layer) ∧
      (∀ entry ∈ node.entries, (entry.key, entry.record) ∈ entries) := by
  induction tree with
  | @step expected name node groups present valid slots _ records pruned _ children =>
    refine ⟨node, present, ?_, group_record slots records⟩
    intro pair hit
    obtain ⟨group, inGroups, inGroup⟩ := List.mem_flatMap.mp hit
    have slot : group.1 ∈ node.slots (expected.getD (node.rootContext layerOf)) := by
      rw [← slots]; exact List.mem_map.mpr ⟨group, inGroups, rfl⟩
    cases shape : group.1 with
    | record key record =>
      have pairEq : pair = (key, record) := List.mem_singleton.mp (records group inGroups key record shape ▸ inGroup)
      let ctx := expected.getD (node.rootContext layerOf)
      rw [shape] at slot
      obtain ⟨entry, entryHit, entryKey, _⟩ := slot_record node.entries
        {ctx with layer := ctx.layer - 1, root := false} node.left slot
      rw [pairEq, ← entryKey]
      exact ((valid.2.1 entry entryHit).1.2.1).le
    | gap next edge =>
      cases edge with
      | none => simp [pruned group inGroups next shape] at inGroup
      | some linked =>
        obtain ⟨childNode, _, lower, _⟩ := children group inGroups next linked shape
        rw [shape] at slot
        exact (lower pair inGroup).trans (MstRouteComplete.child_layer_lt valid slot).le

theorem nonroot_nonempty {layerOf : Key → Nat} {reference : Relation Name (Node Name)}
    {expected : Option Context} {name : Name} {entries : List (Key × Name)}
    (tree : Realizes layerOf reference expected name entries)
    (notRoot : ∃ ctx, expected = some ctx ∧ ctx.root = false) : entries ≠ [] := by
  induction tree with
  | @step expected name node groups _ valid slots _ records _ _ children =>
    obtain ⟨ctx, rfl, lower⟩ := notRoot
    cases first : node.entries with
    | cons head tail =>
      have present := group_record slots records head (by simp [first])
      exact fun empty => by simp [empty] at present
    | nil =>
      have linked : node.left.isSome = true := by
        simpa [lower] using valid.2.2.2 (by simp [first])
      obtain ⟨child, edge⟩ := Option.isSome_iff_exists.mp linked
      let next : Context := {ctx with layer := ctx.layer - 1, root := false}
      have slot : Slot.gap next (some child) ∈ groups.map Prod.fst := by
        rw [slots]
        simp [Node.slots, slotsFrom, next, first, edge]
      obtain ⟨group, present, same⟩ := List.mem_map.mp slot
      have nonempty := children group present next child same ⟨next, rfl, rfl⟩
      intro empty
      apply nonempty
      cases contents : group.2 with
      | nil => rfl
      | cons head tail =>
        have hit : head ∈ groups.flatMap Prod.snd := List.mem_flatMap.mpr ⟨group, present, by simp [contents]⟩
        simp [empty] at hit

theorem root_max {layerOf : Key → Nat} {reference : Relation Name (Node Name)} (bound : Binding reference)
    {name : Name} {entries : List (Key × Name)} (tree : Realizes layerOf reference none name entries)
    {node : Node Name} (known : reference name node) :
    (∀ pair ∈ entries, layerOf pair.1 ≤ (node.rootContext layerOf).layer) ∧
      ((node.rootContext layerOf).layer = 0 ∨ ∃ pair ∈ entries, layerOf pair.1 = (node.rootContext layerOf).layer) := by
  obtain ⟨actual, present, upper, records⟩ := layers tree
  obtain rfl := bound present known
  refine ⟨upper, ?_⟩
  cases first : actual.entries with
  | nil => exact Or.inl (by simp [Node.rootContext, first])
  | cons head tail =>
    exact Or.inr ⟨(head.key, head.record), records head (by simp [first]), by simp [Node.rootContext, first]⟩

end Silmaril.Proofs.Formats.Dasl.MstRooted
