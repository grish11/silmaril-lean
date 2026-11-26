module

public import Silmaril.Formats.Parquet.DeltaBinaryPacked.Defs
import Silmaril.Proofs.Formats.Parquet.DeltaBinaryPacked.Wire
import Silmaril.Proofs.Formats.Parquet.DeltaBinaryPacked.Values

/-! Exact wire coverage, count, and ordered signed-word reconstruction. -/

public section

namespace Silmaril.Formats.Parquet.DeltaBinaryPacked

/-- The checked prefix and the untouched suffix account for the supplied bytes. -/
theorem parsePrefix_sound {physical : Physical} {limits : Limits} {expected : Nat}
    {source : Bytes} {stream : Stream} {rest : List UInt8}
    (h : parsePrefix physical limits expected source = .ok (stream, rest)) :
    source.length ≤ limits.bytes ∧ source.toList = stream.wire ++ rest ∧
      stream.Valid physical limits expected :=
  Proofs.Formats.Parquet.DeltaBinaryPacked.parsePrefix_sound h

theorem parsePrefix_consumed {physical : Physical} {limits : Limits} {expected : Nat}
    {source : Bytes} {stream : Stream} {rest : List UInt8}
    (h : parsePrefix physical limits expected source = .ok (stream, rest)) :
    source.toList.take stream.wire.length = stream.wire ∧
      source.toList.drop stream.wire.length = rest :=
  Proofs.Formats.Parquet.DeltaBinaryPacked.parsePrefix_consumed h

theorem parse_ok_iff {physical : Physical} {limits : Limits} {expected : Nat}
    {source : Bytes} {stream : Stream} :
    parse physical limits expected source = .ok stream ↔
      parsePrefix physical limits expected source = .ok (stream, []) :=
  Proofs.Formats.Parquet.DeltaBinaryPacked.parse_ok_iff

/-- The AST accounts for the entire input and satisfies the checked profile. -/
theorem parse_sound {physical : Physical} {limits : Limits} {expected : Nat}
    {source : Bytes} {stream : Stream} (h : parse physical limits expected source = .ok stream) :
    source.length ≤ limits.bytes ∧ source.toList = stream.wire ∧ stream.Valid physical limits expected :=
  Proofs.Formats.Parquet.DeltaBinaryPacked.parse_sound h

/-- Narrowing yields the balanced residue modulo the physical word size. -/
theorem step_toInt (physical : Physical) (previous : physical.Value) (delta : Int) :
    physical.toInt (physical.step previous delta) =
      (physical.toInt previous + delta).bmod (2 ^ physical.bits) :=
  Proofs.Formats.Parquet.DeltaBinaryPacked.step_toInt physical previous delta

theorem reconstruct_length {physical : Physical} {limits : Limits} {expected : Nat}
    {stream : Stream} (valid : stream.Valid physical limits expected) :
    (stream.reconstruct physical).length = expected :=
  Proofs.Formats.Parquet.DeltaBinaryPacked.reconstruct_length valid

/-- Value `index` folds precisely the preceding deltas in wire order. -/
theorem reconstruct_getElem {stream : Stream} {physical : Physical} {index : Nat}
    (bounded : index < (stream.reconstruct physical).length) :
    (stream.reconstruct physical)[index] =
      (stream.deltas.take index).foldl physical.step (physical.ofInt stream.header.first) :=
  Proofs.Formats.Parquet.DeltaBinaryPacked.reconstruct_getElem bounded

theorem decode_sound {physical : Physical} {limits : Limits} {expected : Nat}
    {source : Bytes} {values : List physical.Value}
    (h : decode physical limits expected source = .ok values) :
    ∃ stream : Stream, source.length ≤ limits.bytes ∧ source.toList = stream.wire ∧
      stream.Valid physical limits expected ∧ values = stream.reconstruct physical ∧
      values.length = expected :=
  Proofs.Formats.Parquet.DeltaBinaryPacked.decode_sound h

end Silmaril.Formats.Parquet.DeltaBinaryPacked
