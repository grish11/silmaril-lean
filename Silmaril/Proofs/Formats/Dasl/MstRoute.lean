module

public import Silmaril.Formats.Dasl.Mst.Route.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl.MstRoute

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.Mst Silmaril.Semantics.Naming

variable {Name : Type}

private theorem before_trans {left mid right : Key} (first : left.before mid) (second : mid.before right) :
    left.before right := lt_trans first second

private theorem before_irrefl (key : Key) : ¬ key.before key := lt_irrefl _

private theorem slots_lower (entries : List (Entry Name))
    (ordered : entries.Pairwise fun left right => left.key.before right.key)
    (ctx : Context) (child : Option Name) (limit : Key) (lower : ctx.lower = some limit)
    (entriesAbove : ∀ entry ∈ entries, limit.before entry.key) :
    ∀ slot ∈ slotsFrom ctx child entries, ∀ key, slot.Covers key → limit.before key := by
  induction entries generalizing ctx child limit with
  | nil =>
    intro slot hit key covered
    have same : slot = .gap ctx child := List.mem_singleton.mp hit
    subst slot
    exact covered.1 limit (by simp [lower])
  | cons head tail ih =>
    intro slot hit key covered
    rcases List.mem_cons.mp hit with same | hit
    · subst slot
      exact covered.1 limit (by simp [lower])
    · rcases List.mem_cons.mp hit with same | hit
      · subst slot
        change key = head.key at covered
        exact covered ▸ entriesAbove head (by simp)
      · obtain ⟨across, tailOrder⟩ := List.pairwise_cons.mp ordered
        exact before_trans (entriesAbove head (by simp))
          (ih tailOrder {ctx with lower := some head.key} head.right head.key rfl across slot hit key covered)

theorem slots_ordered (entries : List (Entry Name)) (ctx : Context) (child : Option Name)
    (ordered : entries.Pairwise fun left right => left.key.before right.key) :
    (slotsFrom ctx child entries).Pairwise
      (fun left right => ∀ first second, left.Covers first → right.Covers second → first.before second) := by
  induction entries generalizing ctx child with
  | nil => simp [slotsFrom]
  | cons head tail ih =>
    obtain ⟨across, tailOrder⟩ := List.pairwise_cons.mp ordered
    apply List.pairwise_cons.mpr
    constructor
    · intro slot hit first second left right
      have below : first.before head.key := left.2 head.key (by simp)
      rcases List.mem_cons.mp hit with same | later
      · subst slot
        change second = head.key at right
        exact right.symm ▸ below
      · have above := slots_lower tail tailOrder {ctx with lower := some head.key} head.right
          head.key rfl across slot later second right
        exact before_trans below above
    · apply List.pairwise_cons.mpr
      refine ⟨?_, ih {ctx with lower := some head.key} head.right tailOrder⟩
      intro slot hit first second left right
      have above := slots_lower tail tailOrder {ctx with lower := some head.key} head.right
        head.key rfl across slot hit second right
      change first = head.key at left
      exact left.symm ▸ above

theorem slots_separated (entries : List (Entry Name)) (ctx : Context) (child : Option Name)
    (ordered : entries.Pairwise fun left right => left.key.before right.key) :
    (slotsFrom ctx child entries).Pairwise (fun left right => ∀ key, left.Covers key → ¬ right.Covers key) :=
  (slots_ordered entries ctx child ordered).imp (fun across key first second =>
    before_irrefl _ (across key key first second))

private theorem lookup_parts (key : Key) (groups : List (SlotEntries Name))
    (separated : (groups.map Prod.fst).Pairwise (fun left right => ∀ sought, left.Covers sought → ¬ right.Covers sought))
    (bounded : ∀ group ∈ groups, ∀ pair ∈ group.2, group.1.Covers pair.1) :
    (groups.flatMap Prod.snd).lookup key =
      (groups.find? fun group => decide (group.1.Covers key)).bind (fun group => group.2.lookup key) := by
  induction groups with
  | nil => rfl
  | cons group tail ih =>
    obtain ⟨across, tailSeparated⟩ := List.pairwise_cons.mp separated
    simp only [List.flatMap_cons, List.lookup_append, List.find?_cons]
    by_cases inside : group.1.Covers key
    · have absent : (tail.flatMap Prod.snd).lookup key = none := by
        apply List.lookup_eq_none_iff.mpr
        intro pair hit
        obtain ⟨part, inTail, inPart⟩ := List.mem_flatMap.mp hit
        have excluded := across part.1 (List.mem_map.mpr ⟨part, inTail, rfl⟩) key inside
        have different : key ≠ pair.1 := fun same =>
          excluded (same.symm ▸ bounded part (List.mem_cons_of_mem _ inTail) pair inPart)
        simpa using different
      simp [inside, absent, Option.or_none]
    · have absent : group.2.lookup key = none := by
        apply List.lookup_eq_none_iff.mpr
        intro pair hit
        have different : key ≠ pair.1 := fun same => inside (same.symm ▸ bounded group (by simp) pair hit)
        simpa using different
      simpa [inside, absent] using ih tailSeparated (fun part hit => bounded part (List.mem_cons_of_mem _ hit))

theorem route_sound {layerOf : Key → Nat} {reference : Relation Name (Node Name)} (bound : Binding reference)
    {read : Name → Wire.ReadResult (Shallow Name)} (sound : ReadSound read reference)
    {expected : Option Context} {name : Name} {entries : List (Key × Name)}
    (tree : Realizes layerOf reference expected name entries) {fuel : Nat} {key : Key} {result : Option Name}
    (checked : route layerOf read key fuel expected name = .ok result) : entries.lookup key = result := by
  induction fuel generalizing expected name entries with
  | zero => simp [route] at checked
  | succ fuel ih =>
    cases tree with
    | @step _ _ node groups known valid shape inside records pruned child =>
      cases first : read name with
      | missing => simp [route, readChecked, first] at checked
      | invalidWire => simp [route, readChecked, first] at checked
      | found value =>
        cases parsed : decodeNode? value with
        | none => simp [route, readChecked, first, parsed] at checked
        | some actual =>
          have same := bound (sound first parsed) known
          subst actual
          simp only [route, readChecked, first, parsed, dite_eq_left valid] at checked
          let ctx := expected.getD (node.rootContext layerOf)
          have locate : matchingSlot node ctx key =
              (groups.find? fun group => decide (group.1.Covers key)).map Prod.fst := by
            rw [matchingSlot, ← shape, List.find?_map]
            rfl
          have separated : (groups.map Prod.fst).Pairwise
              (fun left right => ∀ sought, left.Covers sought → ¬ right.Covers sought) := by
            rw [shape]
            exact slots_separated _ _ _ valid.1
          rw [lookup_parts key groups separated inside]
          change (match matchingSlot node ctx key with
            | none => Except.error (RouteError.invalidNode name)
            | some (.record _ record) => .ok (some record)
            | some (.gap _ none) => .ok none
            | some (.gap ctx (some child)) => route layerOf read key fuel (some ctx) child) = .ok result at checked
          rw [locate] at checked
          cases selection : (groups.find? fun group => decide (group.1.Covers key)) with
          | none => simp [selection] at checked
          | some group =>
            have hit := List.mem_of_find?_eq_some selection
            change group.2.lookup key = result
            cases selected : group.1 with
            | record entry record =>
              have covers : group.1.Covers key := of_decide_eq_true
                (List.find?_some (p := fun part : SlotEntries Name => decide (part.1.Covers key)) selection)
              have keyEq : key = entry := by simpa [selected, Slot.Covers] using covers
              rw [records group hit entry record selected, keyEq]
              simpa [selection, selected] using checked
            | gap next linked =>
              cases linked with
              | none =>
                rw [pruned group hit next selected]
                change none = result
                exact Except.ok.inj (by simpa only [selection, selected, Option.map_some] using checked)
              | some link =>
                apply ih (child group hit next link selected)
                simpa only [selection, selected, Option.map_some] using checked

theorem realizes_mono {layerOf : Key → Nat} {source extension : Relation Name (Node Name)}
    (incl : Subset source extension) {expected : Option Context} {name : Name} {entries : List (Key × Name)}
    (tree : Realizes layerOf source expected name entries) : Realizes layerOf extension expected name entries := by
  induction tree with
  | step present valid slots bounded records pruned child children =>
    exact .step (incl present) valid slots bounded records pruned children

theorem realizes_ordered {layerOf : Key → Nat} {reference : Relation Name (Node Name)}
    {expected : Option Context} {name : Name} {entries : List (Key × Name)}
    (tree : Realizes layerOf reference expected name entries) :
    entries.Pairwise (fun left right => left.1.before right.1) := by
  induction tree with
  | @step expected name node groups present valid slots bounded records pruned child children =>
    apply List.pairwise_flatMap.mpr
    constructor
    · intro group hit
      cases slot : group.1 with
      | record key record => simp [records group hit key record slot]
      | gap ctx child =>
        cases child with
        | none => simp [pruned group hit ctx slot]
        | some link => exact children group hit ctx link slot
    · have ordered := slots_ordered node.entries
        { (expected.getD (node.rootContext layerOf)) with
          layer := (expected.getD (node.rootContext layerOf)).layer - 1, root := false } node.left valid.1
      change (node.slots (expected.getD (node.rootContext layerOf))).Pairwise _ at ordered
      rw [← slots, List.pairwise_map] at ordered
      exact ordered.imp_of_mem (fun inLeft inRight across first firstHit second secondHit =>
        across first.1 second.1 (bounded _ inLeft first firstHit) (bounded _ inRight second secondHit))

end Silmaril.Proofs.Formats.Dasl.MstRoute
