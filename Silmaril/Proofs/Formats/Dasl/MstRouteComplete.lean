module

public import Silmaril.Formats.Dasl.Mst.Route.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl.MstRouteComplete

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.Mst Silmaril.Semantics.Naming

variable {Name : Type}

private theorem key_trichotomy (key separator : Key) : key.before separator ∨ key = separator ∨ separator.before key := by
  rcases lt_trichotomy (key.map UInt8.toFin) (separator.map UInt8.toFin) with less | equal | greater
  · exact Or.inl less
  · exact Or.inr (Or.inl (List.map_inj_right (fun _ _ same => UInt8.toFin_inj.mp same) |>.mp equal))
  · exact Or.inr (Or.inr greater)

private theorem slots_cover (key : Key) (entries : List (Entry Name)) (ctx : Context) (child : Option Name)
    (inside : ctx.Contains key) : ∃ slot ∈ slotsFrom ctx child entries, Slot.Covers slot key := by
  induction entries generalizing ctx child with
  | nil => exact ⟨.gap ctx child, by simp [slotsFrom], inside⟩
  | cons entry tail ih =>
    rcases key_trichotomy key entry.key with below | same | above
    · refine ⟨.gap {ctx with upper := some entry.key} child, by simp [slotsFrom], inside.1, ?_⟩
      simpa using below
    · exact ⟨.record entry.key entry.record, by simp [slotsFrom], same⟩
    · obtain ⟨slot, hit, covers⟩ := ih {ctx with lower := some entry.key} entry.right ⟨by simpa using above, inside.2⟩
      exact ⟨slot, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hit), covers⟩

private theorem linked_gap (entries : List (Entry Name)) (ctx : Context) (left : Option Name)
    {next : Context} {child : Name} (hit : Slot.gap next (some child) ∈ slotsFrom ctx left entries) :
    next.layer = ctx.layer ∧ (left = some child ∨ ∃ entry ∈ entries, entry.right = some child) := by
  induction entries generalizing ctx left with
  | nil =>
    obtain ⟨rfl, same⟩ := Slot.gap.inj (List.mem_singleton.mp hit)
    exact ⟨rfl, Or.inl same.symm⟩
  | cons entry tail ih =>
    rcases List.mem_cons.mp hit with first | later
    · obtain ⟨rfl, same⟩ := Slot.gap.inj first
      exact ⟨rfl, Or.inl same.symm⟩
    · rcases List.mem_cons.mp later with record | rest
      · cases record
      · obtain ⟨layer, fromEntry | ⟨inner, present, edge⟩⟩ := ih {ctx with lower := some entry.key} entry.right rest
        · exact ⟨layer, Or.inr ⟨entry, by simp, fromEntry⟩⟩
        · exact ⟨layer, Or.inr ⟨inner, List.mem_cons_of_mem _ present, edge⟩⟩

theorem child_layer_lt {layerOf : Key → Nat} {node : Node Name} {ctx next : Context} {child : Name}
    (valid : ctx.Valid layerOf node) (hit : Slot.gap next (some child) ∈ node.slots ctx) : next.layer < ctx.layer := by
  obtain ⟨layer, edge⟩ := linked_gap node.entries {ctx with layer := ctx.layer - 1, root := false} node.left hit
  have positive : 0 < ctx.layer := Nat.pos_of_ne_zero fun zero => by
    rcases edge with left | ⟨entry, present, right⟩
    · simpa [left] using valid.2.2.1 zero
    · simpa [right] using (valid.2.1 entry present).2 zero
  change next.layer = ctx.layer - 1 at layer
  omega

theorem route_available {layerOf : Key → Nat} {reference : Relation Name (Node Name)}
    {read : Name → Wire.ReadResult (Shallow Name)} {key : Key} {root : Name}
    (covers : PathCovers layerOf read key root reference)
    {expected : Option Context} {name : Name} {entries : List (Key × Name)}
    (tree : Realizes layerOf reference expected name entries) {fuel : Nat}
    (reached : Reaches layerOf read key root expected name)
    (inside : ∀ ctx ∈ expected, ctx.Contains key)
    (enough : ∀ node, reference name node → (expected.getD (node.rootContext layerOf)).layer < fuel) :
    ∃ result, route layerOf read key fuel expected name = .ok result := by
  induction fuel generalizing expected name entries with
  | zero =>
    cases tree with
    | step present _ _ _ _ _ _ => exact (Nat.not_lt_zero _ (enough _ present)).elim
  | succ fuel ih =>
    cases tree with
    | @step _ _ node groups present valid slots _ _ _ child =>
      let ctx := expected.getD (node.rootContext layerOf)
      obtain ⟨value, found, parsed⟩ := covers reached present
      have inCtx : ctx.Contains key := by
        cases expected with
        | none => simp [ctx, Node.rootContext, Context.Contains]
        | some next => exact inside next (by simp)
      obtain ⟨slot, hit, inSlot⟩ := slots_cover key node.entries
        {ctx with layer := ctx.layer - 1, root := false} node.left inCtx
      have locates : ∃ selected, matchingSlot node ctx key = some selected := by
        unfold matchingSlot
        cases selected : (node.slots ctx).find? (fun part => decide (part.Covers key)) with
        | none => exact ((List.find?_eq_none.mp selected) slot hit (decide_eq_true inSlot)).elim
        | some part => exact ⟨part, rfl⟩
      obtain ⟨selected, located⟩ := locates
      have selectedHit : selected ∈ node.slots ctx := List.mem_of_find?_eq_some located
      have selectedCovers : selected.Covers key := of_decide_eq_true
        (List.find?_some (p := fun part : Slot Name => decide (part.Covers key)) located)
      simp only [route, readChecked, found, parsed, dite_eq_left valid]
      change ∃ result, (match matchingSlot node ctx key with
        | none => Except.error (RouteError.invalidNode name)
        | some (.record _ record) => Except.ok (some record)
        | some (.gap _ none) => Except.ok none
        | some (.gap next (some link)) => route layerOf read key fuel (some next) link) = .ok result
      rw [located]
      cases selected with
      | record _ record => exact ⟨some record, rfl⟩
      | gap next edge =>
        cases edge with
        | none => exact ⟨none, rfl⟩
        | some link =>
          have nextLayer := child_layer_lt valid selectedHit
          change next.layer < ctx.layer at nextLayer
          have enoughHere := enough node present
          change ctx.layer < fuel + 1 at enoughHere
          have enoughChild : next.layer < fuel := by omega
          rw [← slots] at selectedHit
          obtain ⟨group, inGroups, asGap⟩ := List.mem_map.mp selectedHit
          exact ih (child group inGroups next link asGap) (.step reached found parsed valid located)
            (by simpa [Slot.Covers] using selectedCovers) (fun _ _ => enoughChild)

end Silmaril.Proofs.Formats.Dasl.MstRouteComplete
