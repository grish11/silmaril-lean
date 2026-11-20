module

public import Silmaril.Semantics.Prolly.Defs

public section

namespace Silmaril.Proofs.Semantics.Prolly

open Silmaril.Semantics.Prolly

variable {Key Payload Item : Type}

theorem flatten_chunkFrom (cut : Nat → Item → Bool) (current items : List Item) :
    (chunkFrom cut current items).flatten = current ++ items := by
  induction items generalizing current with
  | nil => cases current <;> simp [chunkFrom]
  | cons head tail ih =>
    by_cases boundary : cut (current.length + 1) head <;> simp [chunkFrom, boundary, ih]

theorem count_chunks (cut : Nat → Item → Bool) (noSingle : ∀ count item, cut count item → 2 ≤ count)
    (current items : List Item) : 2 * (chunkFrom cut current items).length ≤ current.length + items.length + 1 := by
  induction items generalizing current with
  | nil => cases current <;> simp [chunkFrom]
  | cons head tail ih =>
    by_cases boundary : cut (current.length + 1) head
    · have enough := noSingle _ _ boundary
      have rest := ih []
      simp [chunkFrom, boundary] at rest ⊢
      omega
    · have rest := ih (current ++ [head])
      simp [chunkFrom, boundary] at rest ⊢
      omega

theorem length_chunk (cut : Nat → Item → Bool) {width : Nat}
    (atWidth : ∀ count item, width ≤ count → cut count item)
    {current items group : List Item} (within : current.length < width)
    (hit : group ∈ chunkFrom cut current items) : group.length ≤ width := by
  induction items generalizing current with
  | nil =>
    cases current with
    | nil => simp [chunkFrom] at hit
    | cons first rest =>
      have same : group = first :: rest := by simpa [chunkFrom] using hit
      exact same.symm ▸ Nat.le_of_lt within
  | cons head tail ih =>
    by_cases boundary : cut (current.length + 1) head
    · rcases List.mem_cons.mp (by simpa [chunkFrom, boundary] using hit) with rfl | rest
      · simp; omega
      · exact ih (by simp; omega) rest
    · have small : current.length + 1 < width := Nat.lt_of_not_ge (boundary ∘ atWidth _ _)
      exact ih (current := current ++ [head]) (by simpa using small) (by simpa [chunkFrom, boundary] using hit)

theorem cut_min (policy : Policy Key) {level count : Nat} {key : Key} (hit : policy.cut level count key) : 2 ≤ count := by
  have minWidth := policy.minWidth
  simp [Policy.cut] at hit
  omega

theorem cut_max (policy : Policy Key) {level count : Nat} {key : Key} (limit : policy.width ≤ count) :
    policy.cut level count key := by simp [Policy.cut, limit]

theorem lift_entries (level : Nat) (chunks : List (Node Key Payload level)) :
    flatten (level + 1) (lift chunks) = flatten level chunks.flatten := by
  induction chunks with
  | nil => cases level <;> rfl
  | cons head tail ih =>
    cases head with
    | nil => simpa [lift, List.filterMap_cons] using ih
    | cons first rest =>
      cases level <;> simp [lift, flatten, List.flatMap_append] at ih ⊢ <;> rw [ih]

theorem grow_entries (policy : Policy Key) (fuel level : Nat) (node : Node Key Payload level) :
    (grow policy fuel level node).entries = flatten level node := by
  induction fuel generalizing level with
  | zero => rfl
  | succ fuel ih =>
    unfold grow
    split
    · rfl
    · rw [ih, lift_entries]
      rw [show (chunk _ node).flatten = node from flatten_chunkFrom _ [] node]

theorem lift_count (chunks : List (List (Key × Item))) : (lift chunks).length ≤ chunks.length :=
  List.length_filterMap_le _ _

private theorem cap {width level : Nat} {node group : Node Key Payload level}
    (children : Node.ChildrenBounded width level node) (within : group.length ≤ width)
    (subset : ∀ child ∈ group, child ∈ node) : Node.Bounded width level group := by
  cases level with
  | zero => exact within
  | succ level => exact ⟨within, fun child hit => children child (subset child hit)⟩

theorem grow_bounded (policy : Policy Key) (fuel level : Nat) (node : Node Key Payload level)
    (enough : node.length ≤ fuel) (children : Node.ChildrenBounded policy.width level node) :
    (grow policy fuel level node).Bounded policy.width := by
  induction fuel generalizing level with
  | zero =>
    change Node.Bounded policy.width level node
    exact cap children (by omega) (fun _ hit => hit)
  | succ fuel ih =>
    unfold grow
    split
    · rename_i within
      exact cap children within (fun _ hit => hit)
    · rename_i wide
      let cut := fun count (pair : Key × Content Key Payload level) => policy.cut level count pair.1
      let groups := chunk cut node
      apply ih (level + 1) (lift groups)
      · have bounded := lift_count groups
        have shrinks := count_chunks cut (fun _ _ boundary => cut_min policy boundary) [] node
        change 2 * groups.length ≤ [].length + node.length + 1 at shrinks
        have := policy.minWidth
        simp only [List.length_nil, Nat.zero_add] at shrinks
        omega
      · intro child hit
        obtain ⟨group, groupHit, same⟩ := List.mem_filterMap.mp hit
        cases group with
        | nil => simp at same
        | cons first rest =>
          cases same
          apply cap children
          · exact length_chunk cut (fun _ _ limit => cut_max policy limit)
              (by have := policy.minWidth; simp; omega) groupHit
          · intro pair inside
            rw [← show groups.flatten = node from flatten_chunkFrom cut [] node]
            exact List.mem_flatten.mpr ⟨_, groupHit, inside⟩

end Silmaril.Proofs.Semantics.Prolly
