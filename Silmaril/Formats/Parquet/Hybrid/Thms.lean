module

public import Silmaril.Formats.Parquet.Hybrid.Defs
import Silmaril.Proofs.Formats.Parquet.Hybrid.Header
import Silmaril.Proofs.Formats.Parquet.Hybrid.Run
import Silmaril.Proofs.Formats.Parquet.Hybrid.Codec

/-! Exact wire consumption, value bounds, and round trips for explicit RLE runs. -/

public section

namespace Silmaril.Formats.Parquet.Hybrid

/-- The bounded reader consumes exactly the canonical ULEB prefix. -/
theorem readULEB_sound {fuel value : Nat} {input rest : List UInt8}
    (h : readULEB fuel input = .ok (value, rest)) : input = uleb value ++ rest :=
  Proofs.Formats.Parquet.Hybrid.readULEB_sound h

/-- A successful split retains both the exact prefix and the remaining bytes. -/
theorem takeExact_ok_iff {size : Nat} {input payload rest : List UInt8} :
    takeExact size input = .ok (payload, rest) ↔
      payload.length = size ∧ input = payload ++ rest :=
  Proofs.Formats.Parquet.Hybrid.takeExact_ok_iff

/-- A valid header consumes exactly its minimal ULEB encoding. -/
theorem readHeader_ok_iff {input rest : List UInt8} {code : Nat} :
    readHeader input = .ok (code, rest) ↔ code < 2 * runLimit ∧ input = uleb code ++ rest :=
  Proofs.Formats.Parquet.Hybrid.readHeader_ok_iff

/-- A successful run scan consumes its header and exact payload. -/
theorem readRun_ok_iff {width : Nat} {input rest : List UInt8} {run : Run} :
    readRun width input = .ok (run, rest) ↔ run.Valid width ∧ input = run.wire width ++ rest :=
  Proofs.Formats.Parquet.Hybrid.readRun_ok_iff

/-- Indexing a group projects the specified bits from its little-endian word. -/
theorem unpackGroup_getElem (width : Nat) (bytes : List UInt8) {i : Nat}
    (hi : i < (unpackGroup width bytes).length) :
    (unpackGroup width bytes)[i] = KBytes.leVal bytes / (2 ^ width) ^ i % (2 ^ width) :=
  Proofs.Formats.Parquet.Hybrid.unpackGroup_getElem width bytes hi

theorem run_values_length (width : Nat) (run : Run) :
    (run.values width).length = run.size :=
  Proofs.Formats.Parquet.Hybrid.run_values_length width run

/-- Successful complete reads are exactly the budgeted wire streams with the given count. -/
theorem decode_ok_iff {width expected : Nat} {limits : Limits} {source : Bytes}
    {values : List Nat} :
    decode width expected limits source = .ok values ↔
      width ≤ 32 ∧ expected < runLimit ∧ expected ≤ limits.values ∧
        source.length ≤ limits.bytes ∧ Wire width expected source.toList values :=
  Proofs.Formats.Parquet.Hybrid.decode_ok_iff

theorem decode_length {width expected : Nat} {limits : Limits} {source : Bytes}
    {values : List Nat} (h : decode width expected limits source = .ok values) :
    values.length = expected :=
  Proofs.Formats.Parquet.Hybrid.decode_length h

theorem decode_values_fit {width expected : Nat} {limits : Limits} {source : Bytes}
    {values : List Nat} (h : decode width expected limits source = .ok values) :
    ∀ n ∈ values, n < 2 ^ width :=
  Proofs.Formats.Parquet.Hybrid.decode_values_fit h

/-- A successful explicit RLE encoding round-trips within the reader budgets. -/
theorem decode_encodeRepeated {width count value : Nat} {source : Bytes} {limits : Limits}
    (encoded : encodeRepeated width count value = .ok source)
    (valuesBound : count ≤ limits.values) (bytesBound : source.length ≤ limits.bytes) :
    decode width count limits source = .ok (List.replicate count value) :=
  Proofs.Formats.Parquet.Hybrid.decode_encodeRepeated encoded valuesBound bytesBound

end Silmaril.Formats.Parquet.Hybrid
