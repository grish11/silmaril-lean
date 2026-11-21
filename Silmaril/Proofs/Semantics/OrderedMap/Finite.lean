module

public import Mathlib.Data.Set.Finite.Basic
public import Silmaril.Semantics.OrderedMap.Finite.Defs
public import Silmaril.Semantics.OrderedMap.Thms

public section

namespace Silmaril.Proofs.Semantics.OrderedMapFinite

open Silmaril.Semantics OrderedMap

variable {Key Item : Type} [LinearOrder Key]

theorem lookup_ofLookupOn (keys : Finset Key) (lookup : Key → Option Item) (key : Key) :
    (ofLookupOn keys lookup).lookup? key = if key ∈ keys then lookup key else none := by
  apply Option.ext
  intro item
  rw [lookup_eq_some_iff]
  change (key, item) ∈ (keys.sort (· ≤ ·)).filterMap
    (fun candidate => (lookup candidate).map (candidate, ·)) ↔ _
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨candidate, mem, hit⟩
    obtain ⟨value, decoded, equal⟩ := Option.map_eq_some_iff.mp hit
    cases equal
    simpa [(Finset.mem_sort _).mp mem] using decoded
  · intro hit
    split at hit
    · exact ⟨key, (Finset.mem_sort _).mpr ‹key ∈ keys›, by simp [hit]⟩
    · cases hit

theorem mem_keySet (map : OrderedMap Key Item) (key : Key) :
    key ∈ map.keySet ↔ (map.lookup? key).isSome := by
  change key ∈ (map.entries.map Prod.fst).toFinset ↔ _
  simp only [List.mem_toFinset, List.mem_map, Option.isSome_iff_exists]
  constructor
  · rintro ⟨⟨entryKey, item⟩, mem, rfl⟩
    exact ⟨item, map.lookup_eq_some_iff.mpr mem⟩
  · rintro ⟨item, hit⟩
    exact ⟨(key, item), map.lookup_eq_some_iff.mp hit, rfl⟩

theorem finite_support_iff (lookup : Key → Option Item) :
    (support lookup).Finite ↔ ∃ map : OrderedMap Key Item, map.lookup? = lookup := by
  constructor
  · intro finite
    refine ⟨ofLookupOn finite.toFinset lookup, funext fun key => ?_⟩
    rw [lookup_ofLookupOn]
    cases hit : lookup key <;> simp [Set.Finite.mem_toFinset, support, hit]
  · rintro ⟨map, rfl⟩
    have equal : support map.lookup? = ↑map.keySet := Set.ext fun key => (mem_keySet map key).symm
    exact equal ▸ map.keySet.finite_toSet

theorem lookup_transport {OtherKey OtherItem : Type} [LinearOrder OtherKey]
    (key : Key ≃ OtherKey) (item : Item ≃ OtherItem) (map : OrderedMap Key Item) (other : OtherKey) :
    (transport key item map).lookup? other = (map.lookup? (key.symm other)).map item := by
  rw [transport, lookup_ofLookupOn]
  have mem : other ∈ map.keySet.map key.toEmbedding ↔ (map.lookup? (key.symm other)).isSome := by
    rw [← mem_keySet, Finset.mem_map]
    constructor
    · rintro ⟨src, hsrc, heq⟩
      convert hsrc using 1
      exact (key.symm_apply_eq.mpr heq.symm)
    · exact fun hsrc => ⟨key.symm other, hsrc, key.apply_symm_apply other⟩
  cases hit : map.lookup? (key.symm other)
  · exact ite_eq_right (fun present => by simpa [hit] using mem.mp present)
  · exact ite_eq_left (mem.mpr (by simp [hit]))

theorem set_lookup (keys : Finset Key) (key : Key) :
    (OrderedSet.ofFinset keys).lookup? key = if key ∈ keys then some () else none := by
  apply Option.ext
  rintro ⟨⟩
  rw [lookup_eq_some_iff]
  change (key, ()) ∈ (keys.sort (· ≤ ·)).map (·, ()) ↔ _
  simp [List.mem_map]

end Silmaril.Proofs.Semantics.OrderedMapFinite
