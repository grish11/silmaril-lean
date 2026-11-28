module

public import Silmaril.Formats.Parquet.DeltaBinaryPacked.Defs
import Silmaril.Proofs.Formats.Parquet.DeltaBinaryPacked.Wire
import Silmaril.Formats.Parquet.Hybrid.Thms
import Init.Data.List.Scan.Lemmas
import Init.Data.SInt.Lemmas
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.DeltaBinaryPacked

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.DeltaBinaryPacked

public theorem step_toInt (physical : Physical) (previous : physical.Value) (delta : Int) :
    physical.toInt (physical.step previous delta) =
      (physical.toInt previous + delta).bmod (2 ^ physical.bits) := by
  cases physical with
  | int32 => exact Int32.toInt_ofInt
  | int64 => exact Int64.toInt_ofInt

private theorem residuals_length {size : Nat} (aligned : size % 32 = 0) (mini : Miniblock) :
    (mini.residuals size).length = size := by
  have groups := Hybrid.run_values_length mini.width.toNat (.packed (size / 8) mini.payload)
  change (mini.residuals size).length = (size / 8) * 8 at groups
  omega

private theorem miniblocks_cover {physical : Physical} {size count : Nat} {minis : List Miniblock}
    (aligned : size % 32 = 0) (layout : MiniblocksFit physical size count minis) :
    count ≤ (minis.flatMap (Miniblock.residuals size)).length := by
  induction layout with
  | done => simp
  | @use remaining mini rest positive width extent fit ih =>
    simp only [List.flatMap_cons, List.length_append, residuals_length aligned]
    omega

private theorem block_deltas_length {physical : Physical} {size : Nat} {block : Block}
    (aligned : size % 32 = 0) (layout : MiniblocksFit physical size block.count block.miniblocks) :
    (block.deltas size).length = block.count := by
  simp only [Block.deltas, List.length_map, List.length_take]
  exact Nat.min_eq_left (miniblocks_cover aligned layout)

private theorem blocks_deltas_length {physical : Physical} {header : Header} {count : Nat}
    {blocks : List Block} (aligned : header.miniblockSize % 32 = 0)
    (layout : BlocksFit physical header count blocks) :
    (blocks.flatMap (Block.deltas header.miniblockSize)).length = count := by
  induction layout with
  | done => rfl
  | @use count block rest positive blockCount minimum widths minis tail ih =>
    have bounded : block.count ≤ count := blockCount ▸ Nat.min_le_left ..
    simp only [List.flatMap_cons, List.length_append, block_deltas_length aligned minis, ih]
    omega

public theorem reconstruct_length {physical : Physical} {limits : Limits} {expected : Nat}
    {stream : Stream} (valid : stream.Valid physical limits expected) :
    (stream.reconstruct physical).length = expected := by
  obtain ⟨count, _, _, _, _, _, aligned, _, _⟩ := valid.geometry
  have deltas := blocks_deltas_length aligned valid.layout
  change stream.deltas.length = stream.header.totalCount - 1 at deltas
  unfold Stream.reconstruct
  split
  · rename_i empty
    simpa only [List.length_nil, empty] using count
  · rename_i nonempty
    rw [List.length_scanl, deltas]
    omega

public theorem reconstruct_getElem {stream : Stream} {physical : Physical} {index : Nat}
    (bounded : index < (stream.reconstruct physical).length) :
    (stream.reconstruct physical)[index] =
      (stream.deltas.take index).foldl physical.step (physical.ofInt stream.header.first) := by
  by_cases empty : stream.header.totalCount = 0
  · simp [Stream.reconstruct, empty] at bounded
  · simp [Stream.reconstruct, empty, List.getElem_scanl]

public theorem decode_sound {physical : Physical} {limits : Limits} {expected : Nat}
    {source : Bytes} {values : List physical.Value}
    (h : decode physical limits expected source = .ok values) :
    ∃ stream : Stream, source.length ≤ limits.bytes ∧ source.toList = stream.wire ∧
      stream.Valid physical limits expected ∧ values = stream.reconstruct physical ∧
      values.length = expected := by
  cases parsed : parse physical limits expected source with
  | error error => simp [decode, parsed, Except.map] at h
  | ok stream =>
    have same : stream.reconstruct physical = values := by
      simpa [decode, parsed, Except.map] using h
    obtain ⟨bytes, wire, valid⟩ := parse_sound parsed
    exact ⟨stream, bytes, wire, valid, same.symm, same ▸ reconstruct_length valid⟩

end Silmaril.Proofs.Formats.Parquet.DeltaBinaryPacked
