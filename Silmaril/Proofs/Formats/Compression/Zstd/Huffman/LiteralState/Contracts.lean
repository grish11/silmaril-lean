module

public import Silmaril.Formats.Compression.Zstd.Huffman.LiteralState.Defs
import Silmaril.Formats.Compression.Zstd.Huffman.LiteralSection.Thms
import Silmaril.Formats.Compression.Zstd.Huffman.TreeDescription.Thms
import Silmaril.Formats.Compression.Zstd.LiteralBlock.Thms

public section

namespace Silmaril.Proofs.Formats.Compression.Zstd.Huffman.LiteralState

open Silmaril.Formats.Compression.Zstd
open Silmaril.Formats.Compression.Zstd.Huffman
open Silmaril.Formats.Compression.Zstd.Huffman.LiteralState
open LiteralSection (Limits Envelope Header)
open LiteralSection.Internal (readFields cutEnvelope readStreams readFields_sound cutEnvelope_sound readStreams_sound)
open Silmaril.Formats.Compression.Zstd.Huffman.LiteralState.Internal

private theorem envelope_sound {limits : Limits} {first : UInt8} {rest : List UInt8} {part : Envelope}
    (h : readEnvelope limits first rest = .ok part) :
    part.Wire (first.toNat % 4) (first :: rest) ∧
      part.header.extent ≤ limits.inputCap ∧ part.header.regenerated ≤ limits.outputCap := by
  cases parsed : readFields first rest with
  | error reason => simp [readEnvelope, parsed, bind, Except.bind] at h
  | ok pair =>
    obtain ⟨header, body⟩ := pair
    simp only [readEnvelope, parsed, bind, Except.bind] at h
    obtain ⟨rfl, slice, extent, inputFits, outputFits⟩ := cutEnvelope_sound h
    obtain ⟨bytes, shape, wire⟩ := readFields_sound parsed
    exact ⟨⟨bytes, shape.trans (congrArg (bytes ++ ·) slice), wire, extent⟩, inputFits, outputFits⟩

private theorem new_sound {limits : Limits} {prior : State limits.tree} {input : List UInt8}
    {part : Envelope} {result : Result limits.tree}
    (envelope : part.Wire 2 input) (inputFits : part.header.extent ≤ limits.inputCap)
    (outputFits : part.header.regenerated ≤ limits.outputCap)
    (h : readNew limits part = .ok result) :
    Wire limits prior input result ∧ result.consumed ≤ limits.inputCap ∧
      result.literals.size ≤ limits.outputCap := by
  unfold readNew at h
  split at h
  · cases h
  rename_i description table checked
  cases decoded : readStreams limits part.header (part.header.compressed - description.consumed)
      description.rest table with
  | error reason => simp [decoded, Except.mapError, bind, Except.bind] at h
  | ok out =>
    simp only [decoded, Except.mapError, bind, Except.bind, pure, Except.pure] at h
    cases h
    obtain ⟨_, valid, _⟩ := TreeDescription.readTable_sound checked
    obtain ⟨wire, count⟩ := readStreams_sound decoded
    have remainder : description.rest.length = part.header.compressed - description.consumed := by
      rw [← TreeDescription.suffix_exact valid.1, List.length_drop]
      obtain ⟨_, _, _, exactBody⟩ := envelope
      rw [exactBody]
    exact ⟨.newTree envelope checked remainder wire count (install_table checked), inputFits, by simpa [LiteralBlock.Literals.size, count] using outputFits⟩

private theorem treeless_sound {limits : Limits} {prior : State limits.tree} {input : List UInt8}
    {part : Envelope} {result : Result limits.tree}
    (envelope : part.Wire 3 input) (inputFits : part.header.extent ≤ limits.inputCap)
    (outputFits : part.header.regenerated ≤ limits.outputCap)
    (h : readTreeless limits prior part = .ok result) :
    Wire limits prior input result ∧ result.consumed ≤ limits.inputCap ∧
      result.literals.size ≤ limits.outputCap := by
  cases available : prior.table with
  | none => simp [readTreeless, available] at h
  | some table =>
    cases decoded : readStreams limits part.header part.header.compressed part.body table with
    | error reason => simp [readTreeless, available, decoded, Except.mapError, bind, Except.bind] at h
    | ok out =>
      simp only [readTreeless, available, decoded, Except.mapError, bind, Except.bind, pure, Except.pure] at h
      cases h
      obtain ⟨wire, count⟩ := readStreams_sound decoded
      exact ⟨.treeless envelope available wire count, inputFits, by simpa [LiteralBlock.Literals.size, count] using outputFits⟩

theorem read_sound {limits : Limits} {prior : State limits.tree} {input : List UInt8}
    {result : Result limits.tree} (success : LiteralState.read limits prior input = .ok result) :
    Wire limits prior input result ∧ result.consumed ≤ limits.inputCap ∧
      result.literals.expand.length = result.literals.size ∧ result.literals.size ≤ limits.outputCap := by
  have extent : result.literals.expand.length = result.literals.size := by
    cases result.literals <;> simp [LiteralBlock.Literals.expand, LiteralBlock.Literals.size]
  suffices Wire limits prior input result ∧ result.consumed ≤ limits.inputCap ∧
      result.literals.size ≤ limits.outputCap by
    exact ⟨this.1, this.2.1, extent, this.2.2⟩
  cases input with
  | nil => cases success
  | cons first rest =>
    simp only [LiteralState.read] at success
    split at success
    · cases parsed : LiteralBlock.parseLiteralsBounded limits.inputCap limits.outputCap (first :: rest) with
      | error reason => simp [parsed, Except.mapError, bind, Except.bind] at success
      | ok plain =>
        simp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at success
        cases success
        obtain ⟨wire, inputFits, outputFits⟩ := LiteralBlock.parseLiteralsBounded_sound parsed
        exact ⟨.plain wire, inputFits, outputFits⟩
    · rename_i compressed
      cases parsed : readEnvelope limits first rest with
      | error reason => simp [parsed, Except.mapError, bind, Except.bind] at success
      | ok part =>
        simp only [parsed, Except.mapError, bind, Except.bind] at success
        obtain ⟨wire, inputFits, outputFits⟩ := envelope_sound parsed
        split at success
        · rename_i fresh
          exact new_sound (fresh ▸ wire) inputFits outputFits success
        · rename_i notFresh
          have reused : first.toNat % 4 = 3 := by omega
          exact treeless_sound (reused ▸ wire) inputFits outputFits success

private theorem envelope_partition {kind : Nat} {input : List UInt8} {part : Envelope}
    (wire : part.Wire kind input) :
    ∃ bytes, input = bytes ++ part.rest ∧ bytes.length = part.header.extent := by
  obtain ⟨header, shape, decoded, bodyLength⟩ := wire
  obtain ⟨_, _, _, _, _, headerLength, _, _⟩ := decoded
  exact ⟨header ++ part.body, by rw [shape, List.append_assoc],
    by rw [List.length_append, Header.extent, headerLength, bodyLength]⟩

theorem consumption_exact {limits : Limits} {prior : State limits.tree} {input : List UInt8}
    {result : Result limits.tree} (wire : Wire limits prior input result) :
    ∃ bytes, input = bytes ++ result.rest ∧ bytes.length = result.consumed := by
  cases wire with
  | plain parsed => exact parsed.2
  | newTree part => exact envelope_partition part
  | treeless part => exact envelope_partition part

theorem unavailable_after_reset {limits : Limits} {first : UInt8} {rest : List UInt8} {part : Envelope}
    (kind : first.toNat % 4 = 3) (bounded : readEnvelope limits first rest = .ok part) :
    LiteralState.read limits (State.empty limits.tree) (first :: rest) = .error .unavailableTable := by
  simp [LiteralState.read, kind, bounded, Except.mapError, bind, Except.bind, readTreeless]

theorem table_checked {profile : TreeDescription.Limits} {state : State profile} {table : SingleStream.Table}
    (available : state.table = some table) :
    ∃ (input : List UInt8) (description : TreeDescription.Prefix), description.Valid profile input ∧ SingleStream.TableWire description.tree table := by
  obtain ⟨input, description, checked⟩ := state.provenance table available
  exact ⟨input, description, (TreeDescription.readTable_sound checked).2⟩

end Silmaril.Proofs.Formats.Compression.Zstd.Huffman.LiteralState
