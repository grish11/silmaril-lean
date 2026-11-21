module

public import Silmaril.Semantics.Rope.Defs

public section

namespace Silmaril.Proofs.Semantics.Rope

open Silmaril.Semantics.Rope

variable {Cell : Type}

private theorem sizes_sum (bias : Bias) (capacity count : Nat) : (sizes bias capacity count).sum = count := by
  have division := Nat.mod_add_div count capacity
  cases bias <;> by_cases empty : count % capacity = 0 <;>
    simp [sizes, empty, Nat.mul_comm, Nat.add_comm] <;> omega

private theorem sizes_mem {bias : Bias} {capacity count amount : Nat} (positive : 0 < capacity)
    (present : amount ∈ sizes bias capacity count) : 0 < amount ∧ amount ≤ capacity := by
  have remainder := Nat.mod_lt count positive
  cases bias <;> by_cases empty : count % capacity = 0 <;>
    simp [sizes, empty, List.mem_replicate, eq_comm, or_comm] at present <;> omega

private theorem sizes_length_lt {bias : Bias} {capacity count : Nat} (wide : 2 ≤ capacity)
    (enough : 2 ≤ count) : (sizes bias capacity count).length < count := by
  have division := Nat.mod_add_div count capacity
  have double := Nat.mul_le_mul_right (count / capacity) wide
  cases bias <;> by_cases empty : count % capacity = 0 <;>
    simp [sizes, empty] <;> omega

private theorem fanout_le (geometry : Geometry) : 2 ≤ geometry.fanout := by
  have positive := Nat.two_pow_pos geometry.exponent
  simp only [Geometry.fanout, Nat.pow_succ]
  omega

theorem payload_lengths (geometry : Geometry) (cells : List Cell) :
    (geometry.pages cells).map List.length = sizes .left geometry.pageSize cells.length :=
  List.map_splitLengths_length _ _ (sizes_sum ..).le

theorem payload_recovers (geometry : Geometry) (cells : List Cell) : (geometry.pages cells).flatten = cells :=
  List.flatten_splitLengths _ _ (sizes_sum ..).ge

theorem ofChildren_pages (nodes : List (Tree Cell)) : (Tree.ofChildren nodes).pages = nodes.flatMap Tree.pages := by
  change (List.ofFn (Tree.pages ∘ fun index : Fin nodes.length => nodes[index.val])).flatten = _
  rw [← List.map_ofFn, List.ofFn_getElem]
  rfl

private theorem parentLayer_pages (geometry : Geometry) (nodes : List (Tree Cell)) :
    (parentLayer geometry nodes).flatMap Tree.pages = nodes.flatMap Tree.pages := by
  let lengths := sizes geometry.bias geometry.fanout nodes.length
  have joined := List.flatten_splitLengths nodes lengths (sizes_sum ..).ge
  have regroup (groups : List (List (Tree Cell))) :
      (groups.flatMap fun group => group.flatMap Tree.pages) = groups.flatten.flatMap Tree.pages := by
    induction groups with
    | nil => rfl
    | cons _ _ ih => simp [List.flatMap_append, ih]
  rw [parentLayer, List.flatMap_map]
  simp only [ofChildren_pages]
  exact (regroup (lengths.splitLengths nodes)).trans (congrArg (List.flatMap Tree.pages) joined)

theorem assemble_pages (geometry : Geometry) (fuel : Nat) (nodes : List (Tree Cell)) :
    (assemble geometry fuel nodes).pages = nodes.flatMap Tree.pages := by
  induction fuel generalizing nodes with
  | zero =>
    rcases nodes with _ | ⟨first, _ | ⟨second, rest⟩⟩ <;> simp [assemble, Tree.pages, ofChildren_pages]
  | succ fuel ih =>
    rcases nodes with _ | ⟨first, _ | ⟨second, rest⟩⟩
    · rfl
    · simp [assemble]
    · rw [assemble, ih, parentLayer_pages]

theorem fromList_pages (geometry : Geometry) (cells : List Cell) : (fromList geometry cells).pages = geometry.pages cells := by
  simp only [fromList, assemble_pages, List.flatMap_map, Tree.pages]
  induction geometry.pages cells with
  | nil => rfl
  | cons _ _ ih => simp [ih]

private theorem parentLayer_bound (geometry : Geometry) (nodes : List (Tree Cell))
    (bounded : ∀ node ∈ nodes, node.WidthBound geometry.fanout) :
    ∀ parent ∈ parentLayer geometry nodes, parent.WidthBound geometry.fanout := by
  let lengths := sizes geometry.bias geometry.fanout nodes.length
  have exactLengths := List.map_splitLengths_length nodes lengths (sizes_sum ..).le
  intro parent present
  obtain ⟨group, groupMem, rfl⟩ := List.mem_map.mp present
  have lengthMem : group.length ∈ lengths := exactLengths ▸ List.mem_map_of_mem groupMem
  have width := sizes_mem (Nat.zero_lt_of_lt (fanout_le geometry)) lengthMem
  refine ⟨width.1, width.2, fun index => bounded _ ?_⟩
  have joined := List.flatten_splitLengths nodes lengths (sizes_sum ..).ge
  exact joined ▸ List.mem_flatten.mpr ⟨group, groupMem, List.getElem_mem index.isLt⟩

private theorem assemble_bound (geometry : Geometry) (fuel : Nat) (nodes : List (Tree Cell))
    (fuelEnough : nodes.length ≤ fuel) (bounded : ∀ node ∈ nodes, node.WidthBound geometry.fanout) :
    (assemble geometry fuel nodes).WidthBound geometry.fanout := by
  induction fuel generalizing nodes with
  | zero =>
    have empty : nodes = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp fuelEnough)
    simp [empty, assemble, Tree.WidthBound]
  | succ fuel ih =>
    rcases nodes with _ | ⟨first, _ | ⟨second, rest⟩⟩
    · trivial
    · exact bounded first List.mem_cons_self
    · rw [assemble]
      apply ih _ _ (parentLayer_bound geometry _ bounded)
      have shrinks := sizes_length_lt (bias := geometry.bias) (fanout_le geometry)
        (show 2 ≤ (first :: second :: rest).length by simp)
      simpa [parentLayer] using (Nat.le_of_lt_succ (lt_of_lt_of_le shrinks fuelEnough))

theorem fromList_bound (geometry : Geometry) (cells : List Cell) :
    (fromList geometry cells).WidthBound geometry.fanout := by
  apply assemble_bound
  · simp
  · intro node hit
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hit
    trivial

private theorem parentLayer_level (geometry : Geometry) (nodes : List (Tree Cell)) (level : Nat)
    (uniform : ∀ node ∈ nodes, node.AtLevel level) :
    ∀ parent ∈ parentLayer geometry nodes, parent.AtLevel (level + 1) := by
  intro parent present
  obtain ⟨group, groupMem, rfl⟩ := List.mem_map.mp present
  intro index
  apply uniform
  have joined := List.flatten_splitLengths nodes (sizes geometry.bias geometry.fanout nodes.length) (sizes_sum ..).ge
  exact joined ▸ List.mem_flatten.mpr ⟨group, groupMem, List.getElem_mem index.isLt⟩

private theorem assemble_level (geometry : Geometry) (fuel : Nat) (nodes : List (Tree Cell)) (level : Nat)
    (uniform : ∀ node ∈ nodes, node.AtLevel level) : ∃ height, (assemble geometry fuel nodes).AtLevel height := by
  induction fuel generalizing nodes level with
  | zero =>
    rcases nodes with _ | ⟨first, _ | ⟨second, rest⟩⟩
    · exact ⟨0, rfl⟩
    · exact ⟨level, uniform first List.mem_cons_self⟩
    · exact ⟨level + 1, fun index => uniform _ (List.getElem_mem index.isLt)⟩
  | succ fuel ih =>
    rcases nodes with _ | ⟨first, _ | ⟨second, rest⟩⟩
    · exact ⟨0, rfl⟩
    · exact ⟨level, uniform first List.mem_cons_self⟩
    · exact ih _ _ (parentLayer_level geometry _ level uniform)

theorem fromList_level (geometry : Geometry) (cells : List Cell) :
    ∃ height, (fromList geometry cells).AtLevel height := by
  apply assemble_level (level := 0)
  intro node hit
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hit
  rfl

end Silmaril.Proofs.Semantics.Rope
