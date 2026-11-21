module

public import Silmaril.Formats.PER.Fibers.Thms
public import Silmaril.Formats.PER.UnionFind.Defs
public import Silmaril.Semantics.OrderedMap.Finite.Thms
import Silmaril.Proofs.Formats.PER.UnionFind

public section

namespace Silmaril.Formats.PER.UnionFind

open Silmaril.Semantics
variable {Key : Type} [LinearOrder Key]

/-- Existing keys are unchanged. A new key starts in its own singleton class. -/
def insert (state : UnionFind Key) (key : Key) : UnionFind Key :=
  if (state.find key).isSome then state else
    ⟨insertLabels state.labels key, Proofs.Formats.PERUnionFind.rooted_insert state.rooted key⟩

def singleton (key : Key) : UnionFind Key := empty.insert key

/-- Keep the left representative. Return `none` if either selected key is
unknown; do not implicitly insert keys. No canonical representative policy. -/
def union (state : UnionFind Key) (left right : Key) : Option (UnionFind Key) :=
  (state.find left).pbind fun keep hit => (state.find right).map fun drop =>
    ⟨mergeLabels state.labels keep drop,
      Proofs.Formats.PERUnionFind.rooted_merge state.rooted (state.rooted hit)⟩

theorem find_root (state : UnionFind Key) {key root : Key} (hit : state.find key = some root) :
    state.find root = some root := state.rooted hit

theorem find_twice (state : UnionFind Key) (key : Key) :
    (state.find key).bind state.find = state.find key := by
  cases hit : state.find key
  · rfl
  · exact state.find_root hit

theorem dom_iff_key (state : UnionFind Key) (key : Key) :
    state.partition.Dom key ↔ key ∈ state.labels.keySet :=
  (fibers_dom state.find key).trans (state.labels.mem_keySet key).symm

/-- Fixed points form a transversal in the existing PER API; no congruence
with external operations is implied. -/
def rootsCanonical (state : UnionFind Key) : PER.Canonical state.partition where
  selected key := state.find key = some key
  supported key hit := ⟨key, hit, hit⟩
  representative := Proofs.Formats.PERUnionFind.roots_representative state

theorem sameClass_spec (state : UnionFind Key) (left right : Key) :
    (state.sameClass left right = some true ↔ state.partition.rel left right) ∧
    (state.sameClass left right = some false ↔
      state.partition.Dom left ∧ state.partition.Dom right ∧ ¬ state.partition.rel left right) ∧
    (state.sameClass left right = none ↔ ¬ (state.partition.Dom left ∧ state.partition.Dom right)) :=
  Proofs.Formats.PERUnionFind.sameClass_spec state left right

theorem insert_known {state : UnionFind Key} {key : Key} (known : state.partition.Dom key) :
    state.insert key = state := by simp [insert, (fibers_dom state.find key).mp known]

theorem insert_missing_rel {state : UnionFind Key} {key : Key} (missing : state.find key = none) (left right : Key) :
    (state.insert key).partition.rel left right ↔ state.partition.rel left right ∨ (left = key ∧ right = key) := by
  have absent : ¬ (state.find key).isSome = true := by simp [missing]
  rw [insert, ite_eq_right absent]
  exact Proofs.Formats.PERUnionFind.insert_missing_rel missing left right

theorem union_isSome (state : UnionFind Key) (left right : Key) :
    (state.union left right).isSome ↔ state.partition.Dom left ∧ state.partition.Dom right := by
  simp only [fibers_dom, partition]
  cases hl : state.find left
  · simp [union, hl]
  · cases hr : state.find right <;> simp [union, hl, hr]

theorem union_lookup {state result : UnionFind Key} {left right keep drop : Key}
    (hl : state.find left = some keep) (hr : state.find right = some drop)
    (hit : state.union left right = some result) (key : Key) :
    result.find key = (state.find key).map (redirect keep drop) := by
  simp [union, Option.pbind_some' hl, hr] at hit; subst result
  exact Proofs.Formats.PERUnionFind.lookup_mergeLabels state.labels keep drop key

/-- The only new pairs connect the two selected old classes. In particular
merging either order gives the same partition, not necessarily the same labels. -/
theorem union_rel_iff {state result : UnionFind Key} {left right : Key}
    (hit : state.union left right = some result) (first second : Key) :
    result.partition.rel first second ↔ state.partition.rel first second ∨
      (state.partition.rel first left ∧ state.partition.rel second right) ∨
      (state.partition.rel first right ∧ state.partition.rel second left) := by
  cases hl : state.find left
  · simp [union, Option.pbind_none' hl] at hit
  cases hr : state.find right <;> simp [union, Option.pbind_some' hl, hr] at hit
  subst result
  exact Proofs.Formats.PERUnionFind.merged_rel hl hr first second

theorem union_support {state result : UnionFind Key} {left right : Key}
    (hit : state.union left right = some result) (key : Key) : result.partition.Dom key ↔ state.partition.Dom key := by
  cases hl : state.find left
  · simp [union, Option.pbind_none' hl] at hit
  cases hr : state.find right <;> simp [union, Option.pbind_some' hl, hr] at hit
  subst result
  simp [partition, find, Proofs.Formats.PERUnionFind.lookup_mergeLabels]

theorem union_comm_partition {state forward backward : UnionFind Key} {left right : Key}
    (hl : state.union left right = some forward) (hr : state.union right left = some backward) :
    forward.partition = backward.partition :=
  PER.ext fun first second => by rw [union_rel_iff hl, union_rel_iff hr, or_comm (a := _ ∧ _)]

end Silmaril.Formats.PER.UnionFind
