module

public import Silmaril.Formats.Dasl.Prolly.Replace.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl.ProllyReplace

open Silmaril.Semantics Silmaril.Semantics.Prolly
open Silmaril.Formats.Dasl.Prolly.RootProfile (replacedMap)

variable {Key Payload : Type}

def redraw [DecidableEq Key] (key : Key) (value : Payload) (entry : Key × Payload) : Key × Payload :=
  (entry.1, if key = entry.1 then value else entry.2)

def redrawNode [DecidableEq Key] (key : Key) (value : Payload) :
    (level : Nat) → Node Key Payload level → Node Key Payload level
  | 0, node => node.map (redraw key value)
  | level + 1, node => node.map (fun entry => (entry.1, redrawNode key value level entry.2))

private theorem chunkFrom_map {Item New : Type} (change : Item → New) (cut : Nat → New → Bool)
    (current items : List Item) :
    chunkFrom cut (current.map change) (items.map change) =
      (chunkFrom (fun count item => cut count (change item)) current items).map (List.map change) := by
  induction items generalizing current with
  | nil => simp [chunkFrom, apply_ite (List.map (List.map change))]
  | cons head tail ih =>
    simp only [List.map_cons, chunkFrom, List.length_map]
    split
    · simpa only [List.map_cons, List.map_append, List.map_nil, List.cons.injEq, true_and] using ih []
    · simpa only [List.map_append, List.map_cons, List.map_nil] using ih (current ++ [head])

private theorem lift_map {Item New : Type} (change : Key × Item → Key × New)
    (keys : ∀ entry, (change entry).1 = entry.1) (groups : List (List (Key × Item))) :
    lift (groups.map (List.map change)) = (lift groups).map (fun group => (group.1, group.2.map change)) := by
  induction groups with
  | nil => rfl
  | cons group groups ih =>
    cases group with
    | nil => exact ih
    | cons head rest =>
      change (((rest.map change).getLastD (change head)).1, change head :: rest.map change) ::
        lift (groups.map (List.map change)) =
          ((rest.getLastD head).1, change head :: rest.map change) :: _
      rw [List.getLastD_map, keys, ih]
      rfl

private theorem grow_redraw [DecidableEq Key] (policy : Policy Key) (key : Key) (value : Payload)
    (fuel level : Nat) (node : Node Key Payload level) :
    grow policy fuel level (redrawNode key value level node) =
      let tree := grow policy fuel level node
      ⟨tree.level, redrawNode key value tree.level tree.root⟩ := by
  induction fuel generalizing level with
  | zero => rfl
  | succ fuel ih =>
    let change : Key × Content Key Payload level → Key × Content Key Payload level := fun entry =>
      match level with
      | 0 => redraw key value entry
      | level + 1 => (entry.1, redrawNode key value level entry.2)
    have keys : ∀ entry, (change entry).1 = entry.1 := by intro entry; cases level <;> rfl
    have redraw_eq : redrawNode key value level node = node.map change := by cases level <;> rfl
    have redraw_lift (groups : List (List (Key × Content Key Payload level))) :
        lift (groups.map (List.map change)) = redrawNode key value (level + 1) (lift groups) := by
      rw [lift_map change keys]
      cases level <;> rfl
    simp only [grow, redraw_eq, List.length_map]
    split <;> rename_i fits
    · rw [ite_eq_left fits]
      exact congrArg (Tree.mk level) redraw_eq.symm
    · rw [ite_eq_right fits]
      have chunked := chunkFrom_map change (fun count pair => policy.cut level count pair.1) [] node
      simp only [List.map_nil, keys] at chunked
      change chunk _ (node.map change) = (chunk _ node).map (List.map change) at chunked
      rw [chunked, redraw_lift]
      exact ih (level + 1) _

theorem build_redraw [LinearOrder Key] (policy : Policy Key) (map : OrderedMap Key Payload) (key : Key) (value : Payload) :
    build policy (replacedMap map key value) =
      let tree := build policy map
      ⟨tree.level, redrawNode key value tree.level tree.root⟩ := by
  unfold build replacedMap
  rw [List.length_map]
  exact grow_redraw policy key value map.entries.length 0 map.entries

/-- A single replacement in an existing leaf with all sibling subtrees shared. -/
inductive Edit (key : Key) (value : Payload) : (level : Nat) →
    Node Key Payload level → Node Key Payload level → Payload → Prop where
  | leaf (earlier suffix : List (Key × Payload)) (previous : Payload) :
      Edit key value 0 (earlier ++ (key, previous) :: suffix) (earlier ++ (key, value) :: suffix) previous
  | branch {level : Nat} (earlier suffix : Node Key Payload (level + 1)) (separator : Key)
      {old next : Node Key Payload level} {previous : Payload} : Edit key value level old next previous →
      Edit key value (level + 1) (earlier ++ (separator, old) :: suffix) (earlier ++ (separator, next) :: suffix) previous

theorem Edit.flatten_split {key : Key} {value previous : Payload} {level : Nat} {old next : Node Key Payload level}
    (edit : Edit key value level old next previous) :
    ∃ earlier suffix, flatten level old = earlier ++ (key, previous) :: suffix ∧
      flatten level next = earlier ++ (key, value) :: suffix := by
  induction edit with
  | leaf earlier suffix previous => exact ⟨earlier, suffix, rfl, rfl⟩
  | branch earlier suffix separator _ ih =>
    obtain ⟨innerPrefix, innerSuffix, oldFlat, nextFlat⟩ := ih
    refine ⟨flatten (_ + 1) earlier ++ innerPrefix, innerSuffix ++ flatten (_ + 1) suffix, ?_, ?_⟩ <;>
      simp [flatten, oldFlat, nextFlat, List.append_assoc]

theorem redraw_eq_self [DecidableEq Key] {key : Key} {value : Payload} {level : Nat} {node : Node Key Payload level}
    (absent : ∀ entry ∈ flatten level node, key ≠ entry.1) : redrawNode key value level node = node := by
  induction level with
  | zero =>
    apply List.map_congr_left (g := id) _ |>.trans (List.map_id _)
    intro entry hit
    simp [redraw, absent entry hit]
  | succ level ih =>
    apply List.map_congr_left (g := id) _ |>.trans (List.map_id _)
    intro entry hit
    have noKey : ∀ leaf ∈ flatten level entry.2, key ≠ leaf.1 := fun leaf leafHit =>
      absent leaf (List.mem_flatMap.mpr ⟨entry, hit, leafHit⟩)
    simp [ih noKey]

private theorem ordered_split [LinearOrder Key] {before focus after : List (Key × Payload)} {entry : Key × Payload}
    (present : entry ∈ focus)
    (ordered : (before ++ focus ++ after).Pairwise (fun left right => left.1 < right.1)) :
    (∀ other ∈ before, entry.1 ≠ other.1) ∧
    focus.Pairwise (fun left right => left.1 < right.1) ∧
    (∀ other ∈ after, entry.1 ≠ other.1) := by
  obtain ⟨orderedLeft, _, later⟩ := List.pairwise_append.mp ordered
  obtain ⟨_, orderedFocus, earlier⟩ := List.pairwise_append.mp orderedLeft
  exact ⟨fun other hit => (ne_of_lt (earlier other hit entry present)).symm, orderedFocus,
    fun other hit => ne_of_lt (later entry (List.mem_append_right _ present) other hit)⟩

theorem Edit.eq_redraw [LinearOrder Key] {key : Key} {value previous : Payload} {level : Nat}
    {old next : Node Key Payload level} (edit : Edit key value level old next previous)
    (ordered : (flatten level old).Pairwise (fun left right => left.1 < right.1)) :
    next = redrawNode key value level old := by
  induction edit with
  | leaf earlier suffix previous =>
    have split := ordered_split (List.mem_singleton_self (key, previous)) (by simpa [flatten, List.append_assoc] using ordered)
    have before := redraw_eq_self (level := 0) (value := value) (node := earlier) split.1
    have after := redraw_eq_self (level := 0) (value := value) (node := suffix) split.2.2
    simp only [redrawNode] at before after ⊢
    rw [List.map_append, List.map_cons, before, after]
    simp [redraw]
  | @branch level earlier suffix separator old next previous edit ih =>
    obtain ⟨innerPrefix, innerSuffix, oldFlat, _⟩ := edit.flatten_split
    have present : (key, previous) ∈ flatten level old := by rw [oldFlat]; simp
    have split := ordered_split (before := flatten (level + 1) earlier) (after := flatten (level + 1) suffix) present
      (by simpa [flatten, List.append_assoc] using ordered)
    have before := redraw_eq_self (value := value) split.1
    have after := redraw_eq_self (value := value) split.2.2
    rw [redrawNode.eq_2] at before after ⊢
    rw [List.map_append, List.map_cons, before, after, ← ih split.2.1]

end Silmaril.Proofs.Formats.Dasl.ProllyReplace
