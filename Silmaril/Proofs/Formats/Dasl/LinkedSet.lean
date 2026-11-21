module

public import Mathlib.Data.List.Forall2
public import Silmaril.Formats.Dasl.LinkedSet.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl.LinkedSet

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.LinkedSet
open Silmaril.Semantics (OrderedMap)

variable {Object Name Source Target : Type}
variable {profile : Profile Object Name} {layout : Layout Name}

private theorem mapM_iff {convert : Source → Option Target} {input : List Source} {output : List Target} :
    input.mapM convert = some output ↔ List.Forall₂ (fun left right => convert left = some right) input output := by
  induction input generalizing output with
  | nil => simp
  | cons head tail ih =>
    simp only [List.mapM_cons, List.forall₂_cons_left_iff, ← ih]
    change ((convert head).bind fun first => (tail.mapM convert).bind fun rest => some (first :: rest)) = some output ↔ _
    simp only [Option.bind_eq_some_iff, Option.some.injEq]
    exact ⟨fun ⟨first, ok, rest, done, same⟩ => ⟨first, rest, ok, done, same.symm⟩,
      fun ⟨first, rest, ok, done, same⟩ => ⟨first, ok, rest, done, same.symm⟩⟩

private theorem mapM_mem {convert : Source → Option Target} {input : List Source} {output : List Target}
    (hit : input.mapM convert = some output) {target : Target} :
    target ∈ output ↔ ∃ source ∈ input, convert source = some target := by
  have related := mapM_iff.mp hit
  clear hit
  induction related with
  | nil => simp
  | cons first _ ih =>
    simp only [List.mem_cons, ih, exists_eq_or_imp, first, Option.some.injEq]
    rw [eq_comm (a := target)]

private theorem mapM_source {convert : Source → Option Target} {input : List Source} {output : List Target}
    (hit : input.mapM convert = some output) {source : Source} (present : source ∈ input) :
    ∃ target ∈ output, convert source = some target := by
  have related := mapM_iff.mp hit
  clear hit
  induction related with
  | nil => simp at present
  | cons first _ ih =>
    rcases List.mem_cons.mp present with rfl | tail
    · exact ⟨_, List.mem_cons_self, first⟩
    · obtain ⟨target, mem, encoded⟩ := ih tail
      exact ⟨target, List.mem_cons_of_mem _ mem, encoded⟩

private theorem mapM_map_of {convert : Source → Option Target} {project : Source → Target}
    {input : List Source} (pointwise : ∀ source ∈ input, convert source = some (project source)) :
    input.mapM convert = some (input.map project) :=
  mapM_iff.mpr (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr pointwise))

private theorem mapM_exists {convert : Source → Option Target} (input : List Source)
    (ready : ∀ source ∈ input, ∃ target, convert source = some target) :
    ∃ output, input.mapM convert = some output := by
  induction input with
  | nil => exact ⟨[], rfl⟩
  | cons head rest ih =>
    obtain ⟨first, firstHit⟩ := ready head (by simp)
    obtain ⟨tail, tailHit⟩ := ih (fun other hit => ready other (by simp [hit]))
    exact ⟨first :: tail, mapM_iff.mpr (.cons firstHit (mapM_iff.mp tailHit))⟩

private theorem entries_iff {entries : List (Key × Link Name)} :
    OrderedMap.ofEntries? entries = some layout ↔ entries = layout.entries := by
  constructor
  · intro hit
    unfold OrderedMap.ofEntries? at hit
    split at hit <;> simp_all
    exact congrArg OrderedMap.entries hit
  · rintro rfl
    exact OrderedMap.ofEntries?_entries layout

private theorem octets_injective : Function.Injective octets := by
  intro ⟨left⟩ ⟨right⟩ same
  have equal := congrArg (List.map UInt8.ofFin) same
  simpa [octets, List.map_map, Function.comp_def] using equal

theorem key_injective {objects : Encode.PartialCodec Object ByteArray} {left right : Item Object} {key : Key}
    (first : key? objects left = some key) (second : key? objects right = some key) : left = right := by
  cases left with
  | object left =>
    obtain ⟨leftBytes, encLeft, rfl⟩ := Option.map_eq_some_iff.mp first
    cases right with
    | object right =>
      obtain ⟨rightBytes, encRight, equal⟩ := Option.map_eq_some_iff.mp second
      have same : rightBytes = leftBytes := octets_injective (List.cons.inj equal).2
      exact congrArg Item.object (objects.functional encLeft (same ▸ encRight))
    | blob right => cases (show (1 : Fin 256) = 0 from (List.cons.inj (Option.some.inj second)).1)
  | blob left =>
    cases first
    cases right with
    | object right =>
      obtain ⟨_, _, equal⟩ := Option.map_eq_some_iff.mp second
      cases (show (0 : Fin 256) = 1 from (List.cons.inj equal).1)
    | blob right =>
      exact congrArg Item.blob (octets_injective (List.cons.inj (Option.some.inj second)).2).symm

variable [DecidableEq Name]

theorem entry_iff {link : Link Name} {entry : Key × Link Name} : profile.entry? link = some entry ↔
    entry.2 = link ∧ profile.preferred entry.1 = some link ∧
      ∃ value, profile.reader.resolve? link = some value ∧ key? profile.objects value = some entry.1 := by
  obtain ⟨key, stored⟩ := entry
  simp only [Profile.entry?, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨value, read, actual, rendered, found⟩
    split at found
    · rename_i preferred
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
      exact ⟨rfl, preferred, value, read, rendered⟩
    · contradiction
  · rintro ⟨rfl, preferred, value, read, rendered⟩
    exact ⟨value, read, key, rendered, by simp [preferred]⟩

private theorem entryForKey_spec {key : Key} {entry : Key × Link Name}
    (hit : profile.entryForKey? key = some entry) : entry.1 = key ∧ profile.entry? entry.2 = some entry := by
  simp only [Profile.entryForKey?, Option.bind_eq_some_iff] at hit
  obtain ⟨link, _, actual, valid, found⟩ := hit
  rcases actual with ⟨actualKey, actualLink⟩
  change (if actualKey = key then some (key, link) else none) = some entry at found
  split at found
  · rename_i same
    obtain rfl := Option.some.inj found
    obtain ⟨rfl, _, _⟩ := entry_iff.mp valid
    exact ⟨rfl, same ▸ valid⟩
  · contradiction

theorem ofKeys_sound {requested : Finset Key} (hit : ofKeys? profile requested = some layout) :
    Valid profile layout ∧ keys layout = requested := by
  obtain ⟨entries, built, accepted⟩ := Option.bind_eq_some_iff.mp hit
  obtain rfl := entries_iff.mp accepted
  have related := (mapM_iff.mp built).imp
    (fun key entry success => (entryForKey_spec success).1.symm)
  have sameKeys : requested.sort = layout.keys := by
    simpa only [OrderedMap.keys, List.forall₂_eq_eq_eq] using (List.forall₂_map_right_iff.mpr related :
      List.Forall₂ Eq requested.sort (layout.entries.map Prod.fst))
  constructor
  · intro entry present
    obtain ⟨_, _, found⟩ := (mapM_mem built).mp present
    exact (entryForKey_spec found).2
  · simp [keys, ← sameKeys]

theorem ofKeys_complete (requested : Finset Key)
    (present : ∀ key ∈ requested, Supported profile key) :
    ∃ result, ofKeys? profile requested = some result := by
  obtain ⟨entries, built⟩ := mapM_exists (convert := profile.entryForKey?) requested.sort
    (fun key hit => present key ((Finset.mem_sort _).mp hit))
  have sameKeys : requested.sort = entries.map Prod.fst := by
    have related := (mapM_iff.mp built).imp (fun key entry success => (entryForKey_spec success).1.symm)
    simpa only [List.forall₂_eq_eq_eq] using
      (List.forall₂_map_right_iff.mpr related : List.Forall₂ Eq requested.sort (entries.map Prod.fst))
  have ordered : entries.Pairwise (fun left right => left.1 < right.1) := by
    rw [← List.pairwise_map, ← sameKeys]
    exact (Finset.sortedLT_sort requested).pairwise
  exact ⟨⟨entries, ordered⟩, Option.bind_eq_some_iff.mpr ⟨entries, built, entries_iff.mpr rfl⟩⟩

theorem normalize_sound {values : List (Item Object)} (hit : normalize? profile values = some layout) :
    Valid profile layout ∧ ∀ value, Member profile layout value ↔ value ∈ values := by
  obtain ⟨requested, collected, built⟩ := Option.bind_eq_some_iff.mp hit
  obtain ⟨valid, same⟩ := ofKeys_sound built
  refine ⟨valid, fun value => ?_⟩
  have keyMem (key : Key) : key ∈ layout.keys ↔ key ∈ requested := by
    simpa [keys] using Finset.ext_iff.mp same key
  constructor
  · rintro ⟨key, present, encoded⟩
    obtain ⟨source, mem, sourceKey⟩ := (mapM_mem collected).mp ((keyMem key).mp present)
    exact key_injective sourceKey encoded ▸ mem
  · intro present
    obtain ⟨key, mem, encoded⟩ := mapM_source collected present
    exact ⟨key, (keyMem key).mpr mem, encoded⟩

theorem normalize_complete (values : List (Item Object))
    (ready : ∀ value ∈ values, ∃ key, key? profile.objects value = some key ∧ Supported profile key) :
    ∃ result, normalize? profile values = some result := by
  obtain ⟨requested, collected⟩ := mapM_exists (convert := key? profile.objects) values (fun value present =>
    let ⟨key, encoded, _⟩ := ready value present
    ⟨key, encoded⟩)
  obtain ⟨result, built⟩ := ofKeys_complete (profile := profile) requested.toFinset (fun key present => by
    obtain ⟨value, contained, encoded⟩ := (mapM_mem collected).mp (List.mem_toFinset.mp present)
    obtain ⟨_, same, supported⟩ := ready value contained
    cases Option.some.inj (encoded.symm.trans same)
    exact supported)
  exact ⟨result, Option.bind_eq_some_iff.mpr ⟨requested, collected, built⟩⟩

theorem decode_valid {value : Shallow Name} (hit : decode? profile value = some layout) : Valid profile layout := by
  simp only [decode?, Option.bind_eq_some_iff] at hit
  obtain ⟨_, _, entries, built, accepted⟩ := hit
  obtain rfl := entries_iff.mp accepted
  intro entry present
  obtain ⟨_, _, found⟩ := (mapM_mem built).mp present
  obtain ⟨rfl, _, _⟩ := entry_iff.mp found
  exact found

theorem recovers (valid : Valid profile layout) : decode? profile (encode layout) = some layout := by
  unfold decode? encode
  rw [linkList.recovers]
  simp only [Option.bind_some, List.mapM_map]
  change (layout.entries.mapM (fun entry => profile.entry? entry.2)).bind OrderedMap.ofEntries? = some layout
  rw [mapM_map_of (project := id) valid, List.map_id, Option.bind_some, OrderedMap.ofEntries?_entries]

theorem eq_of_keys {left right : Layout Name} (validLeft : Valid profile left) (validRight : Valid profile right)
    (same : keys left = keys right) : left = right := by
  apply OrderedMap.eq_of_lookup
  intro key
  have sameMem : key ∈ left.keys ↔ key ∈ right.keys := by
    simpa [keys] using Finset.ext_iff.mp same key
  have equal (first second : Layout Name) (validFirst : Valid profile first) (validSecond : Valid profile second)
      (subset : key ∈ first.keys → key ∈ second.keys) {link : Link Name} (hit : first.lookup? key = some link) :
      second.lookup? key = some link := by
    have inFirst := (first.lookup_eq_some_iff).mp hit
    obtain ⟨⟨_, other⟩, inSecond, rfl⟩ := List.mem_map.mp (subset (List.mem_map_of_mem inFirst))
    have equal := (entry_iff.mp (validFirst _ inFirst)).2.1.symm.trans (entry_iff.mp (validSecond _ inSecond)).2.1
    cases Option.some.inj equal
    exact (second.lookup_eq_some_iff).mpr inSecond
  cases found : left.lookup? key with
  | some link => exact (equal left right validLeft validRight sameMem.mp found).symm
  | none =>
    cases other : right.lookup? key with
    | none => rfl
    | some link =>
      have impossible := equal right left validRight validLeft sameMem.mpr other
      rw [found] at impossible
      cases impossible

theorem supported_of_valid (valid : Valid profile layout) {key : Key} (present : key ∈ keys layout) :
    Supported profile key := by
  obtain ⟨⟨found, link⟩, hit, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp present)
  have accepted := valid _ hit
  have selected := (entry_iff.mp accepted).2.1
  exact ⟨(found, link), by simp [Profile.entryForKey?, selected, accepted]⟩

theorem member_resolves (valid : Valid profile layout) (value : Item Object) :
    Member profile layout value ↔ ∃ key link, key? profile.objects value = some key ∧
      layout.lookup? key = some link ∧ profile.reader.resolve? link = some value := by
  constructor
  · rintro ⟨key, present, encoded⟩
    obtain ⟨⟨_, link⟩, hit, rfl⟩ := List.mem_map.mp present
    obtain ⟨_, _, resolved, read, keyMatches⟩ := entry_iff.mp (valid _ hit)
    cases key_injective keyMatches encoded
    exact ⟨_, link, encoded, layout.lookup_eq_some_iff.mpr hit, read⟩
  · rintro ⟨key, link, encoded, hit, _⟩
    exact ⟨key, List.mem_map_of_mem (layout.lookup_eq_some_iff.mp hit), encoded⟩

theorem eq_of_members {left right : Layout Name} (validLeft : Valid profile left) (validRight : Valid profile right)
    (same : ∀ value, Member profile left value ↔ Member profile right value) : left = right := by
  apply eq_of_keys validLeft validRight
  have subset {first second : Layout Name} (valid : Valid profile first)
      (transfer : ∀ value, Member profile first value → Member profile second value) : keys first ⊆ keys second := by
    intro key present
    obtain ⟨⟨_, link⟩, hit, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp present)
    obtain ⟨_, _, resolved, _, encoded⟩ := entry_iff.mp (valid _ hit)
    obtain ⟨_, contained, equal⟩ := transfer resolved ⟨_, List.mem_map_of_mem hit, encoded⟩
    cases Option.some.inj (encoded.symm.trans equal)
    exact List.mem_toFinset.mpr contained
  exact Finset.Subset.antisymm (subset validLeft (fun value => (same value).mp))
    (subset validRight (fun value => (same value).mpr))

end Silmaril.Proofs.Formats.Dasl.LinkedSet
