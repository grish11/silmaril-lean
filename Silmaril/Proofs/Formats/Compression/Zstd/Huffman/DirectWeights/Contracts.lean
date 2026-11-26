module

public import Silmaril.Formats.Compression.Zstd.Huffman.DirectWeights.Defs

public section

namespace Silmaril.Proofs.Formats.Compression.Zstd.Huffman.DirectWeights

open Silmaril.Formats.Compression.Zstd.Huffman.DirectWeights
open Silmaril.Formats.Compression.Zstd.Huffman.DirectWeights.Internal

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

private theorem complete_sound {limits : Limits} {transmitted : List Nat} {tree : Tree}
    (nonempty : 0 < transmitted.length) (symbols : transmitted.length + 1 ≤ limits.symbolCap)
    (success : complete limits transmitted = .ok tree) :
    CompletionWire transmitted tree ∧ tree.Valid limits := by
  simp only [complete] at success
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
  obtain ⟨atLeastTwo, even⟩ := not_or.mp rankFits
  refine ⟨⟨last, rfl, Nat.zero_lt_succ _, by simpa [depth] using logBounds.1, below, sumEq⟩,
    Nat.zero_lt_succ _, Nat.le_of_not_gt depthFits, ?_, ?_, weightBound, total,
    Nat.le_of_not_gt atLeastTwo, Classical.not_not.mp even⟩
  · simp
    omega
  · simpa using symbols

private theorem unpack_length (packed : List UInt8) : (unpack packed).length = 2 * packed.length := by
  induction packed with
  | nil => rfl
  | cons byte rest ih =>
    simp only [unpack, List.flatMap_cons, List.cons_append, List.nil_append, List.length_cons]
    change (unpack rest).length + 1 + 1 = 2 * (rest.length + 1)
    omega

theorem read_sound {limits : Limits} {input : List UInt8} {result : Prefix}
    (success : read limits input = .ok result) :
    PrefixWire input result ∧ result.tree.Valid limits ∧ result.consumed ≤ limits.byteCap := by
  cases input with
  | nil => cases success
  | cons header body =>
    simp only [Silmaril.Formats.Compression.Zstd.Huffman.DirectWeights.read] at success
    split at success
    · cases success
    rename_i direct
    split at success
    · cases success
    rename_i sizeFits
    split at success
    · cases success
    rename_i countFits
    split at success
    · cases success
    rename_i exactSize
    let count := transmittedCount header
    let size := packedSize count
    let packed := body.take size
    let transmitted := (unpack packed).take count
    have packedLength : packed.length = size := Classical.not_not.mp exactSize
    have readCount : transmitted.length = count := by
      change ((unpack packed).take count).length = count
      rw [List.length_take, unpack_length, packedLength]
      apply Nat.min_eq_left
      unfold size packedSize
      omega
    change (complete limits transmitted).map (fun tree => ⟨tree, 1 + size, body.drop size⟩) = .ok result at success
    cases finished : complete limits transmitted with
    | error reason => simp [finished, Except.map] at success
    | ok tree =>
      simp only [finished, Except.map] at success
      cases success
      have countPositive : 0 < count := by
        unfold count transmittedCount
        omega
      obtain ⟨completion, valid⟩ := complete_sound
        (by rw [readCount]; exact countPositive) (by rw [readCount]; exact Nat.le_of_not_gt countFits) finished
      exact ⟨⟨header, packed, congrArg (header :: ·) (List.take_append_drop size body).symm,
        Nat.le_of_not_gt direct, packedLength, congrArg (1 + ·) packedLength.symm, completion⟩,
        valid, Nat.le_of_not_gt sizeFits⟩

theorem suffix_exact {input : List UInt8} {result : Prefix} (wire : PrefixWire input result) :
    input.drop result.consumed = result.rest := by
  obtain ⟨header, packed, inputEq, _, _, consumed, _⟩ := wire
  rw [inputEq, consumed]
  rw [Nat.add_comm, ← List.length_cons]
  exact List.drop_left

end Silmaril.Proofs.Formats.Compression.Zstd.Huffman.DirectWeights
