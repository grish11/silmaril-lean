module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.Defs

/-! Cross-column scans of the paired reader, compared with independent PyArrow rows. -/

namespace Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy

open Silmaril.Formats.Arrow Silmaril.Relational

private def clean : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-byte-array-legacy-events/legacy-v1-empty-middle.parquet"⟩
private def damaged : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-byte-array-legacy-events/legacy-v1-late-error.parquet"⟩
private def reference : String :=
  include_str "../../../../../tests/formats/parquet-int32-byte-array-legacy/scan-reference.txt"

private abbrev SelectedSchema := Scan.Schema String Kind
private abbrev Keep := (selected : SelectedSchema) → Scan.Predicate selected Value

private def observe {selected : SelectedSchema} (row : Scan.Row selected Value) :
    List (Sum (Option Int32) (Option Bytes)) :=
  List.ofFn fun i =>
    match kind : (selected.kind i).2 with
    | .int32 _ => .inl (cast (congrArg (fun k => Option (Value k)) kind) (row i))
    | .byteArray _ => .inr (cast (congrArg (fun k => Option (Value k)) kind) (row i))

private def ordinalPredicate : Keep := fun _ row =>
  match observe row with
  | .inl (some ordinal) :: _ => some (ordinal.toInt % 13 == 5 || ordinal.toInt % 64 == 0)
  | _ => none

private def payloadPredicate : Keep := fun _ row =>
  match observe row with
  | _ :: .inr payload :: _ => payload.map fun (value : Bytes) => value.length > 8
  | _ => none

private def project (positions : List Nat) (selected : SelectedSchema) : Scan.Projection selected :=
  Scan.Projection.ofArray ((positions.filterMap fun i =>
    if h : i < selected.width then some ⟨i, h⟩ else none).toArray)

private def hex (value : Bytes) : String :=
  let digits := "0123456789abcdef".toList.toArray
  String.ofList (value.toList.flatMap fun byte =>
    [digits[byte.toNat / 16]!, digits[byte.toNat % 16]!])

private def cell : Sum (Option Int32) (Option Bytes) → String
  | .inl value => value.map (fun i => toString i.toInt) |>.getD "-"
  | .inr value => value.map hex |>.getD "-"

private def scan (stream : Events.EventStream String Value Error) (positions : List Nat) (keep : Keep)
    (fields : List (String × Kind)) (expected : Events.Termination Error) : IO (List String) := do
  let .ok ⟨selected, trace⟩ := stream.scan (project positions) keep |
    throw (IO.userError "checked projected source failed to open")
  unless List.ofFn selected.kind == fields do throw (IO.userError "wrong projected field order")
  unless trace.termination == expected do throw (IO.userError "wrong EOS or original indexed error")
  return trace.batches.flatMap fun batch =>
    s!"batch {batch.rowCount}" :: (if selected.width = 0 then [] else
      batch.toRows.map fun row => String.intercalate "," ((observe row).map cell))

private def compare (label : String) (file : Bytes) (outcome : Events.Termination Error) :
    IO (List String) := do
  let stream := readAll {} file "ordinal" "payload"
  let ordinal := ("ordinal", Int32ByteArrayGroup.File.Kind.int32 .required)
  let payload := ("payload", Int32ByteArrayGroup.File.Kind.byteArray .optional)
  let byOrdinal ← scan stream [1] ordinalPredicate [payload] outcome
  let byPayload ← scan stream [0] payloadPredicate [ordinal] outcome
  let repeated ← scan stream [1, 0, 1] ordinalPredicate [payload, ordinal, payload] outcome
  let zero ← scan stream [] payloadPredicate [] outcome
  let unknown ← scan stream [] (fun _ _ => none) [] outcome
  return [s!"{label} ordinal to payload"] ++ byOrdinal ++ [s!"{label} payload to ordinal"] ++ byPayload ++
    [s!"{label} reorder and repeat"] ++ repeated ++ [s!"{label} zero columns"] ++ zero ++
    [s!"{label} unknown"] ++ unknown

#eval do
  let failure : Events.Termination Error :=
    .readError (.byteArray (.page 2 1 "payload" 19 21009 (.decode (.plain (.plain .integerOverflow)))))
  let complete ← compare "clean" clean .eos
  let earlier ← compare "damaged" damaged failure
  unless String.intercalate "\n" (complete ++ earlier) ++ "\n" == reference do
    throw (IO.userError "scan batches differ from the independent PyArrow rows")
  IO.println "Paired scan: cross-column predicates, nulls, projection order, empty batches, and original late error agree"

end Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy
