module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.MixedBooleanFloat.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.MixedBooleanFloat.Defs

/-! Independent files with different page partitions for BOOLEAN and FLOAT. -/

namespace Silmaril.Formats.Parquet.MixedBooleanFloat

open Silmaril.Formats Silmaril.Relational

private def v1 : Bytes := ⟨include_bytes "../../../../data/parquet-mixed-boolean-float/mixed-boolean-float-v1.parquet"⟩
private def v2 : Bytes := ⟨include_bytes "../../../../data/parquet-mixed-boolean-float/mixed-boolean-float-v2.parquet"⟩
private def damaged : Bytes :=
  ⟨include_bytes "../../../../data/parquet-mixed-boolean-float/mixed-boolean-float-v2-bad-length.parquet"⟩

private def observeRow {seen : Scan.Schema String Kind} (value : Scan.Row seen Value) :
    List (Sum (Option Bool) (Option UInt32)) :=
  List.ofFn fun index =>
    match kind : (seen.kind index).2 with
    | .boolean => .inl (cast (congrArg (fun k => Option (Value k)) kind) (value index))
    | .floatBits => .inr (cast (congrArg (fun k => Option (Value k)) kind) (value index))

private def expected : List (Option Bool × Option UInt32) :=
  let boolBase := [some true, none, some false, some false, some true, some true, none, some false]
  let floatBase : List (Option UInt32) :=
    [some 0, none, some 0x80000000, some 0x7FC12345, some 1, some 0xFFC54321, some 0x7F800000, none,
     some 0xFF800000, some 0x3F800000, none, some 0x80000001, some 0x00800000, none, some 0x7F7FFFFF, some 0x80400000]
  (List.range 3).flatMap fun group =>
    (List.range 16).map fun i =>
      (boolBase[i % 8]!.map (· ^^ (group == 1 || (group == 2 && i % 2 == 0))),
        floatBase[i]!.map (· ^^^ (if group == 1 then 0x80000000 else if group == 2 then 1 else 0)))

private def check (label : String) (source : Bytes) (isDamaged : Bool) : IO Unit := do
  let .ok ⟨_, trace⟩ := readAll {} source "enabled" "measurement" |
    throw (IO.userError "cannot open mixed file")
  let rows := trace.rows.map observeRow
  let sizes := trace.batches.map (·.rowCount)
  let expectedRows := expected.map fun (boolean, bits) => [Sum.inl boolean, Sum.inr bits]
  if isDamaged then
    unless rows == expectedRows.take 16 && sizes == [16] do throw (IO.userError "wrong prefix")
    unless trace.termination ==
        .readError (.decode 1 (.scan (.page 1 0 "enabled" 1 265 (.decode (.boolean .lengthMismatch))))) do
      throw (IO.userError "wrong typed read error")
    IO.println s!"{label}: {rows.length} rows, lengthMismatch at group 1 column 0 page 1 header 265"
  else
    unless rows == expectedRows && sizes == [16, 16, 16] && trace.termination == .eos do
      throw (IO.userError "wrong typed readback")
    IO.println s!"{label}: {rows.length} rows in {repr sizes}, EOS"

#eval check "V1" v1 false
#eval check "V2" v2 false
#eval check "damaged V2" damaged true

#guard v2.data[291]! == 2 && damaged.data == v2.data.set! 291 3

-- Change the actual FLOAT page tag while leaving the footer advertisement
-- intact. The already decoded BOOLEAN column of group 1 is never published.
#guard v2.data[375]! == 18
#guard match readAll {} ⟨v2.data.set! 375 0⟩ "enabled" "measurement" with
  | .ok ⟨_, trace⟩ =>
    trace.batches.map (·.rowCount) == [16] &&
      trace.termination == .readError (.decode 1 (.scan (.page 1 1 "measurement" 0 361 (.encoding 0))))
  | .error _ => false

private def openedV1 := openFile {} v1 "enabled" "measurement"
private def openedV2 := openFile {} v2 "enabled" "measurement"

#guard match openedV2 with
  | .ok file => file.boolean.columnOrdinal == 0 && file.boolean.leafOrdinal == 1 &&
      file.float.columnOrdinal == 1 && file.float.leafOrdinal == 2
  | .error _ => false

#guard match openFile {} v2 "measurement" "enabled" with
  | .error (.schema (.bind 0 (.leafMismatch 1 _))) => true
  | _ => false

-- A caller can choose a stricter page-version policy without modifying
-- the binding or scalar callback. Framing caps also preempt callbacks.
#guard match openedV1 with
  | .ok file => FlatColumn.readColumn file.boolean {} { booleanPolicy with versions := .v2Only }
      (decodeBoolean {}) 0 = .error (.page 0 0 "enabled" 0 4 .unsupportedVersion)
  | .error _ => False

#guard match openedV2 with
  | .ok file => FlatColumn.readColumn file.boolean { maxPageBytes := 1 } booleanPolicy
      (decodeBoolean {}) 0 = .error (.page 0 0 "enabled" 0 4 .byteLimit)
  | .error _ => False

private def badLength : FlatColumn.DecodePage Bool Unit := fun _ _ _ _ => .ok []
private def badNulls : FlatColumn.DecodePage Bool Unit := fun _ _ header _ =>
  .ok (List.replicate (FlatColumn.pageSlots header) none)

#guard match openedV2 with
  | .ok file => FlatColumn.readColumn file.boolean {} booleanPolicy badLength 0 =
      .error (.page 0 0 "enabled" 0 4 (.outputCount 4 0))
  | .error _ => False

#guard match openedV2 with
  | .ok file => FlatColumn.readColumn file.boolean {} booleanPolicy badNulls 0 =
      .error (.page 0 0 "enabled" 0 4 .nullCount)
  | .error _ => False

end Silmaril.Formats.Parquet.MixedBooleanFloat
