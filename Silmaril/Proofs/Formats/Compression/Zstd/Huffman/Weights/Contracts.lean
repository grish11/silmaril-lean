module

public import Silmaril.Formats.Compression.Zstd.Huffman.Weights.Defs

public section

namespace Silmaril.Proofs.Formats.Compression.Zstd.Huffman.Weights

open Silmaril.Formats.Compression.Zstd.Huffman.Weights

private theorem slots_le_mass {weight : Nat} {weights : List Nat} (member : weight ∈ weights) :
    slots weight ≤ mass weights := by
  induction weights with
  | nil => cases member
  | cons head tail ih =>
    simp only [mass, List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp member with same | inTail
    · rw [same]
      omega
    · have smaller := ih inTail
      change slots weight ≤ (tail.map slots).sum at smaller
      omega

private theorem weight_le_depth {weight depth : Nat} (fits : slots weight < 2 ^ depth) :
    weight ≤ depth := by
  by_cases zero : weight = 0
  · simp [zero]
  · simp only [slots, zero, ite_false] at fits
    have exponent := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp fits
    omega

theorem complete_sound {limits : Limits} {transmitted : List Nat} {tree : Tree}
    (success : complete limits transmitted = .ok tree) :
    CompletionWire transmitted tree ∧ Valid limits tree := by
  simp only [complete] at success
  split at success
  · cases success
  rename_i lengthFits
  split at success
  · cases success
  split at success
  · cases success
  rename_i positive
  split at success
  · cases success
  rename_i depthFits
  split at success
  · cases success
  rename_i finalFits
  split at success
  · cases success
  rename_i rankFits
  cases success
  let depth := (mass transmitted).log2 + 1
  let remaining := 2 ^ depth - mass transmitted
  let last := remaining.log2 + 1
  have logBounds := (Nat.log2_eq_iff positive).mp rfl
  have below : mass transmitted < 2 ^ depth := logBounds.2
  have lastMass : slots last = remaining := Classical.not_not.mp finalFits
  have sumEq : mass transmitted + slots last = 2 ^ depth := by
    rw [lastMass]
    change mass transmitted + (2 ^ depth - mass transmitted) = 2 ^ depth
    omega
  have weightBound : ∀ weight ∈ transmitted ++ [last], weight ≤ depth := by
    intro weight member
    apply weight_le_depth
    rcases List.mem_append.mp member with written | inferred
    · exact Nat.lt_of_le_of_lt (slots_le_mass written) below
    · rw [List.mem_singleton.mp inferred, lastMass]
      change 2 ^ depth - mass transmitted < 2 ^ depth
      omega
  have total : mass (transmitted ++ [last]) = 2 ^ depth := by
    simpa [mass, List.map_append, List.sum_append] using sumEq
  obtain ⟨capFits, dropped⟩ := not_or.mp lengthFits
  have lengthBound := List.drop_eq_nil_iff.mp (Classical.not_not.mp dropped)
  have nonempty : 0 < transmitted.length := by
    cases transmitted with
    | nil => simp [mass] at positive
    | cons head tail => simp
  obtain ⟨atLeastTwo, even⟩ := not_or.mp rankFits
  refine ⟨⟨last, rfl, Nat.zero_lt_succ _, by simpa [depth] using logBounds.1, below, sumEq⟩,
    Nat.zero_lt_succ _, Nat.le_of_not_gt depthFits, ?_, ?_, weightBound, total,
    Nat.le_of_not_gt atLeastTwo, Classical.not_not.mp even⟩
  · simp
    omega
  · simp only [List.length_append, List.length_singleton]
    omega

theorem complete_of_valid {limits : Limits} {transmitted : List Nat} {tree : Tree}
    (wire : CompletionWire transmitted tree) (valid : Valid limits tree) :
    complete limits transmitted = .ok tree := by
  obtain ⟨last, weightsEq, lastPositive, lower, upper, total⟩ := wire
  obtain ⟨depthPositive, depthBound, minLength, maxLength, allBound, _, minRank, evenRank⟩ := valid
  have lengthBound : transmitted.length ≤ limits.symbolCap - 1 := by
    rw [weightsEq, List.length_append, List.length_singleton] at maxLength
    omega
  have capBound := Nat.le_trans minLength maxLength
  have weightsBound : (transmitted.all fun weight => decide (weight ≤ limits.depthCap)) = true := by
    apply List.all_eq_true.mpr
    intro weight mem
    exact decide_eq_true (Nat.le_trans (allBound weight (weightsEq ▸ List.mem_append_left _ mem)) depthBound)
  have positive : 0 < mass transmitted := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) lower
  have logDepth : (mass transmitted).log2 = tree.depth - 1 :=
    (Nat.log2_eq_iff (Nat.ne_of_gt positive)).mpr ⟨lower, by simpa [Nat.sub_add_cancel depthPositive] using upper⟩
  have exactDepth : (mass transmitted).log2 + 1 = tree.depth := by omega
  have exactMass : 2 ^ tree.depth - mass transmitted = slots last := by omega
  have power : slots last = 2 ^ (last - 1) := by simp [slots, Nat.ne_of_gt lastPositive]
  have exactLast : ((slots last).log2 + 1) = last := by
    rw [power, Nat.log2_two_pow, Nat.sub_add_cancel lastPositive]
  simp [complete, Nat.not_lt.mpr capBound, List.drop_eq_nil_iff.mpr lengthBound, weightsBound,
    Nat.ne_of_gt positive, exactDepth, Nat.not_lt.mpr depthBound, exactMass, exactLast,
    ← weightsEq, Nat.not_lt.mpr minRank, evenRank]

end Silmaril.Proofs.Formats.Compression.Zstd.Huffman.Weights
