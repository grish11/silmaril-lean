module

public import Silmaril.Formats.PER.Fibers.Thms
public import Silmaril.Formats.PER.UnionFind.Defs
public import Silmaril.Semantics.OrderedMap.Finite.Thms

public section

namespace Silmaril.Proofs.Formats.PERUnionFind

open Silmaril.Formats PER Silmaril.Semantics UnionFind

variable {Key : Type} [LinearOrder Key]

theorem lookup_insertLabels (labels : OrderedMap Key Key) (key member : Key) :
    (insertLabels labels key).lookup? member = if member = key then some key else labels.lookup? member := by
  rw [insertLabels, OrderedMap.lookup_ofLookupOn]
  by_cases same : member = key
  · simp [same]
  · cases old : labels.lookup? member <;> simp [same, old]

theorem rooted_insert {labels : OrderedMap Key Key} (rooted : Rooted labels.lookup?) (key : Key) :
    Rooted (insertLabels labels key).lookup? := by
  intro member root hit
  rw [lookup_insertLabels] at hit ⊢
  split at hit
  · cases Option.some.inj hit; simp
  · by_cases same : root = key
    · simp [same]
    · simp [same, rooted hit]

theorem lookup_mergeLabels (labels : OrderedMap Key Key) (keep drop member : Key) :
    (mergeLabels labels keep drop).lookup? member = (labels.lookup? member).map (redirect keep drop) := by
  apply Option.ext
  intro root
  rw [OrderedMap.lookup_eq_some_iff, Option.map_eq_some_iff]
  change (member, root) ∈ (labels.entries.map _) ↔ _
  rw [List.mem_map]
  constructor
  · rintro ⟨⟨entry, old⟩, mem, equal⟩
    obtain ⟨same, newRoot⟩ := Prod.mk.inj equal
    subst entry
    exact ⟨old, labels.lookup_eq_some_iff.mpr mem, newRoot⟩
  · rintro ⟨old, hit, rfl⟩
    exact ⟨(member, old), labels.lookup_eq_some_iff.mp hit, rfl⟩

theorem rooted_merge {labels : OrderedMap Key Key} (rooted : Rooted labels.lookup?) {keep drop : Key}
    (known : labels.lookup? keep = some keep) : Rooted (mergeLabels labels keep drop).lookup? := by
  intro member root hit
  rw [lookup_mergeLabels] at hit ⊢
  obtain ⟨old, before, rfl⟩ := Option.map_eq_some_iff.mp hit
  by_cases same : old = drop
  · simp [redirect, same, known]
  · simp [redirect, same, rooted before]

theorem roots_representative (state : UnionFind Key) (member : Key) (present : state.partition.Dom member) :
    ∃! root, state.find root = some root ∧ state.partition.rel member root := by
  obtain ⟨root, hit⟩ := (PER.ofDecoder_dom state.find member).mp present
  have fixed := state.rooted hit
  refine ⟨root, ⟨fixed, root, hit, fixed⟩, ?_⟩
  rintro other ⟨otherFixed, label, memberHit, otherHit⟩
  rw [hit] at memberHit
  rw [otherFixed] at otherHit
  exact (Option.some.inj otherHit).trans (Option.some.inj memberHit).symm

theorem sameClass_spec (state : UnionFind Key) (left right : Key) :
    (state.sameClass left right = some true ↔ state.partition.rel left right) ∧
    (state.sameClass left right = some false ↔
      state.partition.Dom left ∧ state.partition.Dom right ∧ ¬ state.partition.rel left right) ∧
    (state.sameClass left right = none ↔ ¬ (state.partition.Dom left ∧ state.partition.Dom right)) := by
  change (_ ↔ (PER.ofDecoder state.find).rel left right) ∧ _
  simp only [UnionFind.partition, PER.ofDecoder_dom, UnionFind.sameClass]
  cases leftHit : state.find left <;> cases rightHit : state.find right <;>
    simp [PER.ofDecoder, leftHit, rightHit, eq_comm]

theorem insert_missing_rel {state : UnionFind Key} {key : Key} (missing : state.find key = none)
    (left right : Key) :
    (fibers (insertLabels state.labels key).lookup?).rel left right ↔
      state.partition.rel left right ∨ (left = key ∧ right = key) := by
  change state.labels.lookup? key = none at missing
  have noLabel : ∀ source, some key ≠ state.labels.lookup? source :=
    fun _ hit => by have fixed := state.rooted hit.symm; rw [missing] at fixed; cases fixed
  change (∃ label, _ = some label ∧ _ = some label) ↔
    (∃ label, state.labels.lookup? left = some label ∧ state.labels.lookup? right = some label) ∨ _
  rw [lookup_insertLabels, lookup_insertLabels]
  by_cases first : left = key <;> by_cases second : right = key <;>
    simp [first, second, missing, noLabel, eq_comm]

theorem merged_rel {labels : OrderedMap Key Key} {left right keep drop : Key}
    (leftHit : labels.lookup? left = some keep) (rightHit : labels.lookup? right = some drop)
    (first second : Key) :
    (fibers (mergeLabels labels keep drop).lookup?).rel first second ↔
      (fibers labels.lookup?).rel first second ∨
      ((fibers labels.lookup?).rel first left ∧ (fibers labels.lookup?).rel second right) ∨
      ((fibers labels.lookup?).rel first right ∧ (fibers labels.lookup?).rel second left) := by
  have redirect_eq (firstRoot secondRoot : Key) :
      redirect keep drop firstRoot = redirect keep drop secondRoot ↔
        firstRoot = secondRoot ∨ (firstRoot = keep ∧ secondRoot = drop) ∨
          (firstRoot = drop ∧ secondRoot = keep) := by
    by_cases firstDrops : firstRoot = drop <;> by_cases secondDrops : secondRoot = drop <;>
      simp [redirect, firstDrops, secondDrops]
    grind
  change (∃ root, _ = some root ∧ _ = some root) ↔ _
  rw [lookup_mergeLabels, lookup_mergeLabels]
  cases firstHit : labels.lookup? first <;> cases secondHit : labels.lookup? second <;>
    simp [PER.ofDecoder, firstHit, secondHit, leftHit, rightHit, redirect_eq, eq_comm]

end Silmaril.Proofs.Formats.PERUnionFind
