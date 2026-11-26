module

public import Silmaril.Formats.Compression.Zstd.CheckedFrame.Defs
import Silmaril.Formats.Compression.Zstd.LiteralBlock.Thms

public section

namespace Silmaril.Proofs.Formats.Compression.Zstd.CheckedFrame

open Silmaril.Formats.Compression.Zstd (Header blockMaximum parseHeader magic contentChecksum)
open Silmaril.Formats.Compression.Zstd.CheckedFrame
open Silmaril.Formats.Compression.Zstd.CheckedFrame.Internal

private theorem takeExact_sound {size : Nat} {input body rest : List UInt8}
    (success : takeExact size input = .ok (body, rest)) :
    input = body ++ rest ∧ body.length = size := by
  simp only [takeExact, List.splitAt_eq] at success
  split at success
  · rename_i length
    cases success
    exact ⟨(List.take_append_drop size input).symm, length⟩
  · cases success

theorem readBlock_sound {header : Header} {remaining : Nat} {input out rest : List UInt8}
    {last : Bool} (success : readBlock header remaining input = .ok (last, out, rest)) :
    BlockWire header input last out rest ∧ out.length ≤ remaining := by
  match input with
  | [] | [_] | [_, _] => cases success
  | first :: second :: third :: bytes =>
    simp only [readBlock] at success
    split at success
    · simp [throw, bind, Except.bind] at success
    · rename_i fits
      have blockFits := Nat.le_of_not_gt fits
      split at success
      · simp [throw, bind, Except.bind] at success
      · rename_i notReserved
        split at success
        · rename_i compressed
          cases sliced : takeExact (BlockHeader.ofBytes first second third).size bytes with
          | error err => simp [sliced, bind, Except.bind] at success
          | ok pair =>
            obtain ⟨body, tail⟩ := pair
            cases expanded : Silmaril.Formats.Compression.Zstd.LiteralBlock.decode header remaining body with
            | error err => simp [sliced, expanded, Except.mapError, bind, Except.bind] at success
            | ok decoded =>
              simp only [sliced, expanded, Except.mapError, bind, Except.bind, pure, Except.pure]
                at success
              cases success
              obtain ⟨shape, extent⟩ := takeExact_sound sliced
              obtain ⟨literals, wire, rfl, _, outFits, budget⟩ :=
                Silmaril.Formats.Compression.Zstd.LiteralBlock.decode_sound expanded
              refine ⟨⟨first, second, third, body, by rw [shape], rfl, blockFits, outFits, ?_⟩, budget⟩
              rw [compressed]
              exact .compressed extent wire
        · rename_i notCompressed
          split at success
          · simp [throw] at success
          · rename_i remainingFits
            have withinBudget := Nat.le_of_not_gt remainingFits
            split at success
            · rename_i raw
              cases sliced : takeExact (BlockHeader.ofBytes first second third).size bytes with
              | error err => simp [sliced, bind, Except.bind] at success
              | ok pair =>
                obtain ⟨body, tail⟩ := pair
                simp only [sliced, bind, Except.bind, pure, Except.pure] at success
                cases success
                obtain ⟨shape, extent⟩ := takeExact_sound sliced
                refine ⟨⟨first, second, third, out, by rw [shape], rfl, blockFits,
                  extent ▸ blockFits, ?_⟩, extent ▸ withinBudget⟩
                rw [raw, ← extent]
                exact .raw out
            · rename_i notRaw
              have kindBound : (BlockHeader.ofBytes first second third).kind < 4 :=
                Nat.mod_lt _ (by decide)
              have rle : (BlockHeader.ofBytes first second third).kind = 1 := by omega
              cases bytes with
              | nil => cases success
              | cons byte tail =>
                cases success
                refine ⟨⟨first, second, third, [byte], rfl, rfl, blockFits,
                  by simpa using blockFits, ?_⟩, by simpa using withinBudget⟩
                rw [rle]
                exact .rle _ byte

theorem readBlocks_sound {header : Header} {fuel remaining : Nat} {input rest : List UInt8}
    {acc final : List (List UInt8)}
    (success : readBlocks header fuel remaining input acc = .ok (final, rest)) :
    ∃ chunks, BlocksWire header input chunks rest ∧
      chunks.flatten.length ≤ remaining ∧ final = acc.reverse ++ chunks := by
  induction fuel generalizing remaining input rest acc final with
  | zero => cases success
  | succ fuel ih =>
    cases read : readBlock header remaining input with
    | error err => simp [readBlocks, read, bind, Except.bind] at success
    | ok triple =>
      obtain ⟨last, out, tail⟩ := triple
      obtain ⟨wire, outFits⟩ := readBlock_sound read
      simp only [readBlocks, read, bind, Except.bind] at success
      cases last with
      | true =>
        cases success
        exact ⟨[out], .last wire, by simpa using outFits, by simp⟩
      | false =>
        obtain ⟨chunks, blocks, remainingFits, shape⟩ := ih success
        refine ⟨out :: chunks, .next wire blocks, ?_, ?_⟩
        · simp only [List.flatten_cons, List.length_append]
          omega
        · simpa [List.reverse_cons, List.append_assoc] using shape

private theorem finish_sound {header : Header} {out trailer result : List UInt8}
    (success : finish header out trailer = .ok result) :
    result = out ∧ (∀ n, header.contentSize = some n → out.length = n) ∧
      trailer = (if header.checksum then contentChecksum out else []) := by
  simp only [finish] at success
  split at success
  · simp [throw, bind, Except.bind] at success
  · rename_i sizeMatches
    have size : ∀ n, header.contentSize = some n → out.length = n := by
      intro n declared
      exact (show n = out.length by simpa [declared] using sizeMatches).symm
    split at success
    · rename_i checksummed
      cases sliced : takeExact 4 trailer with
      | error err => simp [sliced, bind, Except.bind] at success
      | ok pair =>
        obtain ⟨checksum, rest⟩ := pair
        obtain ⟨shape, _⟩ := takeExact_sound sliced
        simp only [sliced, bind, Except.bind] at success
        split at success
        · simp [throw] at success
        · rename_i checksumMatches
          cases rest with
          | cons byte rest => cases success
          | nil =>
            cases success
            exact ⟨rfl, size, by simpa [checksummed] using shape.trans (by simpa using checksumMatches)⟩
    · rename_i noChecksum
      cases trailer with
      | cons byte rest => cases success
      | nil =>
        cases success
        exact ⟨rfl, size, by simp [noChecksum]⟩

theorem decode_sound {limits : Limits} {input out : List UInt8}
    (success : decode limits input = .ok out) :
    ∃ header, FrameWire input out header ∧ input.length ≤ limits.input ∧
      out.length ≤ limits.output ∧ header.windowSize ≤ limits.window := by
  simp only [decode] at success
  split at success
  · simp [throw, bind, Except.bind] at success
  · rename_i inputFits
    cases signatureRead : takeExact 4 input with
    | error err => simp [signatureRead, bind, Except.bind] at success
    | ok pair =>
      obtain ⟨signature, frameData⟩ := pair
      obtain ⟨inputShape, _⟩ := takeExact_sound signatureRead
      simp only [signatureRead, bind, Except.bind] at success
      split at success
      · simp [throw] at success
      · rename_i magicMatches
        have signatureEq : signature = magic := by simpa using magicMatches
        cases parsed : parseHeader frameData with
        | none => simp [parsed, throw] at success
        | some fields =>
          obtain ⟨header, blocks⟩ := fields
          simp only [parsed] at success
          split at success
          · simp [throw] at success
          · rename_i dictionary
            split at success
            · simp [throw] at success
            · rename_i windowFits
              cases read : readBlocks header (input.length / 3) limits.output blocks [] with
              | error err => simp [read] at success
              | ok pair =>
                obtain ⟨decoded, trailer⟩ := pair
                simp only [read] at success
                obtain ⟨chunks, wire, budget, shape⟩ := readBlocks_sound read
                have decodedEq : decoded = chunks := by simpa using shape
                subst decoded
                obtain ⟨rfl, size, trailerWire⟩ := finish_sound success
                exact ⟨header, ⟨frameData, blocks, trailer, chunks,
                  signatureEq ▸ inputShape, parsed, by simpa using dictionary,
                  wire, rfl, size, trailerWire⟩,
                  Nat.le_of_not_gt inputFits, budget, Nat.le_of_not_gt windowFits⟩

end Silmaril.Proofs.Formats.Compression.Zstd.CheckedFrame
