module

public import Silmaril.Formats.Compression.Zstd.Huffman.DirectWeights.Defs

import Silmaril.Formats.Compression.Zstd.Huffman.Weights.Thms

public section

namespace Silmaril.Proofs.Formats.Compression.Zstd.Huffman.DirectWeights

open Silmaril.Formats.Compression.Zstd.Huffman.DirectWeights
open Silmaril.Formats.Compression.Zstd.Huffman.DirectWeights.Internal

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
    change (complete limits transmitted).map
      (fun tree => ⟨tree, 1 + size, body.drop size⟩) = .ok result at success
    cases finished :
      Silmaril.Formats.Compression.Zstd.Huffman.Weights.complete limits.weightLimits transmitted with
    | error reason => simp [complete, finished, Except.mapError, Except.map] at success
    | ok tree =>
      simp only [complete, finished, Except.mapError, Except.map] at success
      cases success
      obtain ⟨completion, valid⟩ := Silmaril.Formats.Compression.Zstd.Huffman.Weights.complete_sound finished
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
