module

public import Silmaril.Formats.Dasl.NameLinkSet.Defs
import Silmaril.Semantics.OrderedMap.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl.NameLinkSet

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.NameLinkSet Silmaril.Semantics

variable {Key Name Value : Type} [LinearOrder Key]

theorem names_ofFinset (requested : Finset Key) : names (ofFinset requested) = requested := by
  ext name
  simp [names, ofFinset, OrderedMap.keys]

theorem ofFinset_names (layout : Layout Key) : ofFinset (names layout) = layout := by
  have sorted : layout.keys.Pairwise (· ≤ ·) := List.pairwise_map.mpr (layout.ordered.imp le_of_lt)
  have recovered : (names layout).sort = layout.keys :=
    (List.toFinset_sort (· ≤ ·) layout.keys_nodup).mpr sorted
  apply OrderedMap.ext
  change ((names layout).sort).map (·, ()) = layout.entries
  rw [recovered]
  simp [OrderedMap.keys, List.map_map, Function.comp_def]

theorem cardinality_eq (layout : Layout Key) : cardinality layout = (names layout).card :=
  (List.toFinset_card_of_nodup layout.keys_nodup).symm

theorem decode_exact [DecidableEq Name] (key : Encode.TotalCodec Key (Link Name))
    {repr : Shallow Name} {layout : Layout Key} (hit : (codec key).decode? repr = some layout) :
    linkArray.decode? repr = some (links key layout) := by
  unfold codec at hit
  obtain ⟨_, seen, parsed⟩ := Option.bind_eq_some_iff.mp hit
  obtain ⟨_, _, retained⟩ := Option.bind_eq_some_iff.mp parsed
  split at retained <;> simp_all

theorem wire_decode_admitted [DecidableEq Name] (profile : Wire.Profile Name) (accept : Link Name → Bool)
    (key : Encode.TotalCodec Key (Link Name)) {layout : Layout Key} {bytes : ByteArray}
    (hit : (wireCodec profile accept key).decode? bytes = some layout) :
    profile.decode? (codec key) bytes = some layout ∧ supported key accept layout = true := by
  change (profile.decode? (codec key) bytes).bind
    (fun set => if supported key accept set then some set else none) = some layout at hit
  obtain ⟨_, _, retained⟩ := Option.bind_eq_some_iff.mp hit
  split at retained <;> simp_all

theorem supported_kinds_disjoint {format : Silmaril.Formats.Cbor.Drisl.CidProfile}
    (name : Silmaril.Formats.Cbor.Drisl.Cid format)
    (object : Wire.linkSupported (.obj name) = true) : Wire.linkSupported (.blob name) = false := by
  simp only [Wire.linkSupported, beq_iff_eq] at object
  simp [Wire.linkSupported, object]

private theorem sortedAt {entries : Array Key} (ordered : entries.toList.Pairwise (· < ·))
    {first second : Nat} (firstFits : first < entries.size) (secondFits : second < entries.size)
    (before : first < second) : entries[first] < entries[second] := by
  have sorted := List.pairwise_iff_getElem.mp ordered first second firstFits secondFits before
  rwa [Array.getElem_toList, Array.getElem_toList] at sorted

theorem search_iff (entries : Array Key) (ordered : entries.toList.Pairwise (· < ·))
    (query : Key) (start width : Nat) (fits : start + width ≤ entries.size) :
    search entries query start width fits = true ↔
      ∃ position, start ≤ position ∧ position < start + width ∧
        ∃ valid : position < entries.size, entries[position] = query := by
  induction width using Nat.strong_induction_on generalizing start with
  | ind width smaller =>
    rw [search]
    split
    · rename_i nonempty
      let pivot := start + width / 2
      have pivotFits : pivot < entries.size := by dsimp [pivot]; omega
      change (if query < entries[pivot] then search entries query start (width / 2) (by omega)
        else if entries[pivot] < query then
          search entries query (pivot + 1) (width - width / 2 - 1) (by dsimp [pivot]; omega)
        else true) = true ↔ _
      split
      · rename_i less
        rw [smaller (width / 2) (by omega)]
        constructor
        · rintro ⟨pos, lo, hi, hit⟩
          exact ⟨pos, lo, by omega, hit⟩
        · rintro ⟨pos, lo, hi, valid, hit⟩
          refine ⟨pos, lo, ?_, valid, hit⟩
          change pos < pivot
          by_contra! after
          rcases lt_or_eq_of_le after with after | equal
          · exact (not_lt_of_ge (sortedAt ordered pivotFits valid after).le) (hit.symm ▸ less)
          · subst pos
            exact (lt_irrefl query) (hit ▸ less)
      · rename_i notLess
        split
        · rename_i greater
          rw [smaller (width - width / 2 - 1) (by omega)]
          dsimp [pivot]
          constructor
          · rintro ⟨pos, lo, hi, hit⟩
            exact ⟨pos, by omega, by omega, hit⟩
          · rintro ⟨pos, lo, hi, valid, hit⟩
            refine ⟨pos, ?_, by omega, valid, hit⟩
            change pivot + 1 ≤ pos
            by_contra! before
            rcases lt_or_eq_of_le (show pos ≤ pivot by omega) with before | equal
            · exact (not_lt_of_ge (sortedAt ordered valid pivotFits before).le) (hit.symm ▸ greater)
            · subst pos
              exact (lt_irrefl query) (hit ▸ greater)
        · rename_i notGreater
          exact ⟨fun _ => ⟨pivot, by dsimp [pivot]; omega, by dsimp [pivot]; omega, pivotFits,
            le_antisymm (le_of_not_gt notLess) (le_of_not_gt notGreater)⟩, fun _ => rfl⟩
    · rename_i empty
      constructor
      · intro impossible
        cases impossible
      · rintro ⟨position, lo, hi, _⟩
        omega

theorem contains_iff (layout : Layout Key) (query : Key) :
    (index layout).contains query = true ↔ query ∈ names layout := by
  rw [Index.contains, search_iff _ (index layout).ordered]
  simp [names, index, List.mem_iff_getElem]

theorem lookup_of_mem (layout : Layout Key) (key : Encode.TotalCodec Key (Link Name))
    (read : Link Name → Resolution Value) {query : Key} (member : query ∈ names layout) :
    (index layout).lookup key read query = some (read (key.encode query)) := by
  simp [Index.lookup, (contains_iff layout query).mpr member]

theorem lookup_none_iff (layout : Layout Key) (key : Encode.TotalCodec Key (Link Name))
    (read : Link Name → Resolution Value) (query : Key) :
    (index layout).lookup key read query = none ↔ query ∉ names layout := by
  simp [Index.lookup, ← contains_iff layout query]

theorem lookup_eq_some_iff (layout : Layout Key) (key : Encode.TotalCodec Key (Link Name))
    (read : Link Name → Resolution Value) (query : Key) (result : Resolution Value) :
    (index layout).lookup key read query = some result ↔
      query ∈ names layout ∧ read (key.encode query) = result := by
  by_cases member : query ∈ names layout
  · simp [lookup_of_mem layout key read member, member]
  · simp [(lookup_none_iff layout key read query).mpr member, member]

theorem contents_ofContents (key : Encode.TotalCodec Key (Link Name))
    {rel : Naming.Relation (Link Name) Value} {chooseName : Value → Key} {values : Finset Value}
    (binding : Naming.Binding rel) (coherent : Coherent key rel chooseName values) :
    contents key rel (ofContents chooseName values) = (↑values : Set Value) := by
  ext value
  change (∃ name ∈ names (ofContents chooseName values), rel (key.encode name) value) ↔ value ∈ values
  simp only [ofContents, names_ofFinset, Finset.mem_image]
  constructor
  · rintro ⟨name, ⟨original, member, rfl⟩, resolved⟩
    rwa [binding resolved (coherent original member)]
  · exact fun member => ⟨chooseName value, ⟨value, member, rfl⟩, coherent value member⟩

variable {Object : Type}

theorem decodedBindings_binding (profile : Wire.Profile Name) (accept : Link Name → Bool)
    (objects : Encode.TotalCodec Object (Shallow Name)) {store : Naming.Relation Name ByteArray}
    (binding : Naming.Binding store) : Naming.Binding (decodedBindings profile accept objects store) := by
  rintro link left right ⟨_, first, readFirst, decodeFirst⟩ ⟨_, second, readSecond, decodeSecond⟩
  rw [binding readFirst readSecond, decodeSecond] at decodeFirst
  exact (Option.some.inj decodeFirst).symm

theorem wireReader_sound (profile : Wire.Profile Name) (accept : Link Name → Bool)
    (objects : Encode.TotalCodec Object (Shallow Name)) {read : Name → Option ByteArray}
    {store : Naming.Relation Name ByteArray}
    (observed : ∀ ⦃name bytes⦄, read name = some bytes → store name bytes) :
    Sound (wireReader profile accept objects read) (decodedBindings profile accept objects store) := by
  intro link value hit
  unfold wireReader at hit
  split at hit
  · rename_i admitted
    split at hit
    · cases hit
    · rename_i bytes seen
      split at hit
      · cases hit
      · rename_i decoded recovered
        cases hit
        exact ⟨admitted, bytes, observed seen, recovered⟩
  · cases hit

end Silmaril.Proofs.Formats.Dasl.NameLinkSet
