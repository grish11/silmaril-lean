module

public import Silmaril.Formats.Parquet.DeltaBinaryPacked.Defs
import Silmaril.Formats.Parquet.Hybrid.Thms
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.DeltaBinaryPacked

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.DeltaBinaryPacked

private theorem bind_ok {ε α β : Type} {action : Except ε α} {next : α → Except ε β}
    {output : β} (h : (action >>= next) = .ok output) :
    ∃ input, action = .ok input ∧ next input = .ok output := by
  cases action with
  | error error => cases h
  | ok value => exact ⟨value, rfl, h⟩

private theorem mapError_ok {ε δ α : Type} {action : Except ε α} {f : ε → δ} {out : α}
    (h : action.mapError f = .ok out) : action = .ok out := by
  cases action with
  | error error => cases h
  | ok value =>
    cases h
    rfl

private theorem readUnsigned_sound {bits value : Nat} {input rest : List UInt8}
    (h : Internal.readUnsigned bits input = .ok (value, rest)) :
    value < 2 ^ bits ∧ input = Hybrid.uleb value ++ rest := by
  unfold Internal.readUnsigned at h
  obtain ⟨⟨code, tail⟩, read, h⟩ := bind_ok h
  change (if code < 2 ^ bits then Except.ok (code, tail)
    else .error (Error.wire .headerOverflow)) = .ok (value, rest) at h
  by_cases fits : code < 2 ^ bits
  · rw [ite_eq_left fits] at h
    cases h
    exact ⟨fits, Hybrid.readULEB_sound (mapError_ok read)⟩
  · rw [ite_eq_right fits] at h
    contradiction

private theorem readHeader_sound {physical : Physical} {input rest : List UInt8} {header : Header}
    (h : Internal.readHeader physical input = .ok (header, rest)) :
    header.CodesFit physical ∧ input = header.wire ++ rest := by
  unfold Internal.readHeader at h
  obtain ⟨⟨_, _⟩, size, h⟩ := bind_ok h
  obtain ⟨⟨_, _⟩, minis, h⟩ := bind_ok h
  obtain ⟨⟨_, _⟩, count, h⟩ := bind_ok h
  obtain ⟨⟨_, _⟩, first, h⟩ := bind_ok h
  obtain ⟨sizeBound, sizeBytes⟩ := readUnsigned_sound size
  obtain ⟨miniBound, miniBytes⟩ := readUnsigned_sound minis
  obtain ⟨countBound, countBytes⟩ := readUnsigned_sound count
  obtain ⟨firstBound, firstBytes⟩ := readUnsigned_sound first
  cases h
  refine ⟨⟨sizeBound, miniBound, countBound, firstBound⟩, ?_⟩
  rw [sizeBytes, miniBytes, countBytes, firstBytes]
  simp [Header.wire, List.append_assoc]

private theorem validateHeader_sound {limits : Limits} {header : Header} {expected : Nat}
    (h : Internal.validateHeader limits expected header = .ok ()) : header.Valid limits expected := by
  unfold Internal.validateHeader at h
  split at h
  · contradiction
  · rename_i count
    split at h
    · contradiction
    · rename_i bounds
      split at h
      · contradiction
      · rename_i geometry
        simp only [Header.Valid]
        refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega,
          by omega, by omega⟩

private theorem readMiniblocks_sound {physical : Physical} {size count : Nat}
    {widths input unused rest : List UInt8} {minis : List Miniblock}
    (h : Internal.readMiniblocks physical size widths count input = .ok (minis, unused, rest)) :
    widths = minis.map Miniblock.width ++ unused ∧
    input = minis.flatMap Miniblock.payload ++ rest ∧ MiniblocksFit physical size count minis := by
  induction widths generalizing count input unused rest minis with
  | nil =>
    cases count with
    | zero =>
      cases h
      exact ⟨rfl, rfl, .done⟩
    | succ => contradiction
  | cons width widths ih =>
    cases count with
    | zero =>
      cases h
      exact ⟨rfl, rfl, .done⟩
    | succ count =>
      unfold Internal.readMiniblocks at h
      split at h
      · contradiction
      · rename_i widthBound
        obtain ⟨⟨payload, tail⟩, taken, h⟩ := bind_ok h
        obtain ⟨⟨minis, unused, rest⟩, read, h⟩ := bind_ok h
        obtain ⟨payloadLength, payloadBytes⟩ := Hybrid.takeExact_ok_iff.mp (mapError_ok taken)
        obtain ⟨widthBytes, remainingBytes, fit⟩ := ih read
        cases h
        refine ⟨?_, ?_, .use (by omega) (Nat.le_of_not_gt widthBound) payloadLength fit⟩
        · simp only [List.map_cons, List.cons_append, List.cons.injEq, true_and]
          exact widthBytes
        · simpa only [List.flatMap_cons, List.append_assoc, ← remainingBytes] using payloadBytes

private theorem readBlock_sound {physical : Physical} {header : Header} {count : Nat}
    {input rest : List UInt8} {block : Block}
    (h : Internal.readBlock physical header count input = .ok (block, rest)) :
    block.count = count ∧ block.minimumCode < 2 ^ physical.bits ∧
    block.miniblocks.length + block.unusedWidths.length = header.miniblockCount ∧
    MiniblocksFit physical header.miniblockSize block.count block.miniblocks ∧
    input = block.wire ++ rest := by
  unfold Internal.readBlock at h
  obtain ⟨⟨minimum, _⟩, minRead, h⟩ := bind_ok h
  obtain ⟨⟨widths, _⟩, taken, h⟩ := bind_ok h
  obtain ⟨⟨minis, unused, rest⟩, read, h⟩ := bind_ok h
  obtain ⟨minBound, minBytes⟩ := readUnsigned_sound minRead
  obtain ⟨widthCount, tableBytes⟩ := Hybrid.takeExact_ok_iff.mp (mapError_ok taken)
  obtain ⟨widthBytes, payloadBytes, fit⟩ := readMiniblocks_sound read
  cases h
  refine ⟨rfl, minBound, ?_, fit, ?_⟩
  · simpa only [widthBytes, List.length_append, List.length_map] using widthCount
  · rw [minBytes, tableBytes, widthBytes, payloadBytes]
    simp [Block.wire, List.append_assoc]

private theorem readBlocks_zero {physical : Physical} {header : Header} {fuel : Nat}
    {input : List UInt8} {reversed output : List Block}
    (h : Internal.readBlocks physical header fuel 0 input reversed = .ok output) :
    ∃ blocks, output = reversed.reverse ++ blocks ∧ input = blocks.flatMap Block.wire ∧
      BlocksFit physical header 0 blocks ∧ blocks.length ≤ fuel := by
  cases input with
  | nil =>
    have same : reversed.reverse = output := by simpa [Internal.readBlocks] using h
    exact ⟨[], by simpa using same.symm, rfl, .done, Nat.zero_le _⟩
  | cons => simp [Internal.readBlocks] at h

private theorem readBlocks_sound {physical : Physical} {header : Header} {fuel remaining : Nat}
    {input : List UInt8} {reversed output : List Block}
    (h : Internal.readBlocks physical header fuel remaining input reversed = .ok output) :
    ∃ blocks, output = reversed.reverse ++ blocks ∧ input = blocks.flatMap Block.wire ∧
      BlocksFit physical header remaining blocks ∧ blocks.length ≤ fuel := by
  induction fuel generalizing remaining input reversed with
  | zero =>
    cases remaining with
    | zero => exact readBlocks_zero h
    | succ => contradiction
  | succ fuel ih =>
    cases remaining with
    | zero => exact readBlocks_zero h
    | succ remaining =>
      unfold Internal.readBlocks at h
      obtain ⟨⟨block, rest⟩, read, h⟩ := bind_ok h
      obtain ⟨count, minBound, widths, minis, blockBytes⟩ := readBlock_sound read
      obtain ⟨blocks, values, tailBytes, fit, budget⟩ := ih h
      rw [← count] at fit
      refine ⟨block :: blocks, ?_, ?_, .use (by omega) count minBound widths minis fit,
        Nat.succ_le_succ budget⟩
      · simpa [List.reverse_cons, List.append_assoc] using values
      · rw [blockBytes, tailBytes, List.flatMap_cons]

public theorem parse_sound {physical : Physical} {limits : Limits} {expected : Nat}
    {source : Bytes} {stream : Stream} (h : parse physical limits expected source = .ok stream) :
    source.length ≤ limits.bytes ∧ source.toList = stream.wire ∧ stream.Valid physical limits expected := by
  unfold parse at h
  split at h
  · contradiction
  · rename_i bytes
    split at h
    · contradiction
    · rename_i values
      obtain ⟨⟨header, _⟩, read, h⟩ := bind_ok h
      obtain ⟨validated, checked, h⟩ := bind_ok h
      cases validated
      obtain ⟨output, readBlocks, h⟩ := bind_ok h
      obtain ⟨codes, headerBytes⟩ := readHeader_sound read
      obtain ⟨blocks, output, blockBytes, fit, bounded⟩ := readBlocks_sound readBlocks
      cases h
      simp only [List.reverse_nil, List.nil_append] at output
      subst output
      refine ⟨by omega, ?_, ⟨by omega, validateHeader_sound checked, codes, fit, bounded⟩⟩
      rw [headerBytes, blockBytes]
      rfl

end Silmaril.Proofs.Formats.Parquet.DeltaBinaryPacked
