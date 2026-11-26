module

import Silmaril.Semantics.BTreePages.Thms
import Mathlib.Data.Nat.Basic

namespace Silmaril.Semantics.BTreePages

open BTree

private def left : Node Nat String 1 :=
  ⟨[(4, [(2, "two"), (4, "four")]), (8, [(6, "six")])], [(10, "ten")]⟩

private def right : Node Nat String 1 :=
  ⟨[(20, [(13, "thirteen"), (20, "twenty")])], [(24, "twenty-four")]⟩

private def sample : Tree Nat String := ⟨2, ⟨[(12, left)], right⟩⟩

private theorem sample_valid : sample.Valid := by
  simp [sample, left, right, Tree.Valid, Node.ValidWithin, ValidChildren, InRange, List.pairwise_cons]

private abbrev Data := PageData Nat String Position
private abbrev Memory := Page.MapMemory Position Data

private def model : Page.Model Position Data Memory := ⟨Page.mapStore _ _, fun _ _ => False⟩
private def layout : Layout Position := (7 :: ·)
private def otherTree : Tree Nat String := ⟨0, [(42, "other")]⟩
private def otherLayout : Layout Position := fun _ => [8]
private def sharedTree : Tree Nat String := ⟨0, [(2, "two"), (4, "four")]⟩
private def sharedLayout : Layout Position := fun _ => [7, 0, 0]

private def memory : Memory
  | 7 :: path => (pageAt layout sample path).elim .absent .defined
  | [8] => .defined (.leaf otherTree.root)
  | [99] => .undef
  | _ => .absent

private theorem represented : Represents model.store layout sample memory := by
  refine ⟨⟨sample_valid, fun _ _ _ _ eq => (List.cons.inj eq).2⟩, ?_⟩
  intro path data found
  change memory (7 :: path) = .defined data
  simp [memory, found]

private theorem leaf_represented (root : Node Nat String 0) (place : Layout Position)
    (valid : (⟨0, root⟩ : Tree Nat String).Valid) (read : memory (place []) = .defined (.leaf root)) :
    Represents model.store place ⟨0, root⟩ memory := by
  refine ⟨⟨valid, ?_⟩, ?_⟩
  · intro left right leftHere rightHere _
    cases left <;> cases right <;> first | rfl | exact (leftHere rfl).elim | exact (rightHere rfl).elim
  · intro position data found
    cases position with
    | nil => cases found; exact read
    | cons => cases found

private theorem other_represented : Represents model.store otherLayout otherTree memory :=
  leaf_represented otherTree.root otherLayout (by simp [otherTree, Tree.Valid, Node.ValidWithin, InRange]) rfl

private theorem shared_represented : Represents model.store sharedLayout sharedTree memory :=
  leaf_represented sharedTree.root sharedLayout
    (by simp [sharedTree, Tree.Valid, Node.ValidWithin, InRange]) rfl

-- These construct two branch reads and a leaf read with the ordinary page rules.
example : Page.Run model (lookup 4 2 [7]) memory [] (.returned (some "four") memory) := by
  refine .call (.readDefined (p := [7]) rfl) ?_
  refine .call (.readDefined (p := [7, 0]) rfl) ?_
  refine .call (.readDefined (p := [7, 0, 0]) rfl) ?_
  exact .pure

example : Page.Run model (lookup 6 2 [7]) memory [] (.returned (some "six") memory) := by
  refine .call (.readDefined (p := [7]) rfl) ?_
  refine .call (.readDefined (p := [7, 0]) rfl) ?_
  refine .call (.readDefined (p := [7, 0, 1]) rfl) ?_
  exact .pure

example : Page.Run model (lookup 24 2 [7]) memory [] (.returned (some "twenty-four") memory) := by
  refine .call (.readDefined (p := [7]) rfl) ?_
  refine .call (.readDefined (p := [7, 1]) rfl) ?_
  refine .call (.readDefined (p := [7, 1, 1]) rfl) ?_
  exact .pure

example : Page.Run model (lookup 12 2 [7]) memory [] (.returned none memory) := by
  refine .call (.readDefined (p := [7]) rfl) ?_
  refine .call (.readDefined (p := [7, 0]) rfl) ?_
  refine .call (.readDefined (p := [7, 0, 2]) rfl) ?_
  exact .pure

example : model.store.lookup memory [98] = .absent := rfl
example : model.store.lookup memory [99] = .undef := rfl

example : Page.Run model (lookup 2 0 [99]) memory [] (.stopped (.ub (.readUndef [99]))) :=
  .ub (.readUndef rfl)

private theorem disjoint : ∀ page, Footprint layout sample page → ¬ Footprint otherLayout otherTree page := by
  rintro page ⟨path, _, rfl⟩ ⟨_, _, address⟩
  cases address

example (edits out) : Page.Run model (lookup 24 2 [7]) memory edits out ↔
    edits = [] ∧ out = .returned (some "twenty-four") memory :=
  lookup_orderedMap_run_iff represented 24

example : ∃ common, Represents model.store layout sample common ∧ Represents model.store otherLayout otherTree common := by
  obtain ⟨common, first, second, _⟩ :=
    (shared_representation_iff represented.1 other_represented.1 memory).mpr (compatible_of_disjoint disjoint)
  exact ⟨common, first, second⟩

-- Changing the unrelated leaf to UNDEF keeps the full result and the new memory.
example (edits out) :
    let changed := model.store.set memory [8] .undef
    Page.Run model (lookup 12 2 [7]) changed edits out ↔ edits = [] ∧ out = .returned none changed := by
  apply lookup_frame_of_disjoint represented disjoint (key := 12)
  intro page outside
  exact (model.store.lookup_set_other memory [8] page .undef (fun eq => outside ⟨[], by simp [atPath], eq.symm⟩)).symm

-- A separate root can observe a leaf already reachable from the multi-level root.
example : Footprint layout sample [7, 0, 0] ∧ Footprint sharedLayout sharedTree [7, 0, 0] :=
  ⟨⟨[0, 0], (by intro h; cases h), rfl⟩, ⟨[], (by intro h; cases h), rfl⟩⟩

example {final edits} (run : Page.Run model (lookup 4 2 [7]) memory edits (.returned (some "four") final)) :
    Represents model.store sharedLayout sharedTree final :=
  shared_lookup_preserves represented shared_represented 4 run

example : ¬ WellFormed (fun _ => (0 : Nat)) sample := by
  intro valid
  have samePosition := valid.2 [] [0] (by intro h; cases h) (by intro h; cases h) rfl
  cases samePosition

end Silmaril.Semantics.BTreePages
