module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.Defs

/-! Both producer columns in the same original V1 groups and the late indexed errors. -/

namespace Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy

open Silmaril.Formats.Arrow Silmaril.Relational

private def clean : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-byte-array-legacy-events/legacy-v1-empty-middle.parquet"⟩
private def damaged : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-byte-array-legacy-events/legacy-v1-late-error.parquet"⟩

private def expected (row : Nat) : Int32ByteArrayGroup.Row :=
  let binary := if row % 13 == 5 then none else
    let digits := toString row
    let padded := String.ofList (List.replicate (4 - digits.length) '0' ++ digits.toList)
    let value := if row < 256 then
      if row % 2 == 0 then "repeat-a" else "repeat-b"
    else "distinct-" ++ padded ++ "-" ++ String.join (List.replicate 4 "opaque-value-")
    some (⟨value.toUTF8⟩ : Bytes)
  (some (Int32.ofNat row), binary)

private def observeRow {selected : Scan.Schema String Kind} (row : Scan.Row selected Value) :
    List (Sum (Option Int32) (Option Bytes)) :=
  List.ofFn fun i =>
    match kind : (selected.kind i).2 with
    | .int32 _ => .inl (cast (congrArg (fun k => Option (Value k)) kind) (row i))
    | .byteArray _ => .inr (cast (congrArg (fun k => Option (Value k)) kind) (row i))

private def limits : Limits := { file := { maxFileRows := 768 } }

private def verify (input : Bytes) (groups : List (List Int32ByteArrayGroup.Row))
    (outcome : Events.Termination Error) : IO Unit := do
  let .ok ⟨selected, trace⟩ := readAll limits input "ordinal" "payload" |
    throw (IO.userError "source failed to open")
  unless List.ofFn selected.kind == [("ordinal", .int32 .required), ("payload", .byteArray .optional)] do
    throw (IO.userError "wrong selected schema")
  let observed := trace.batches.map fun batch => batch.toRows.map observeRow
  let reference := groups.map fun group => group.map fun pair => [Sum.inl pair.1, Sum.inr pair.2]
  unless observed == reference && trace.batches.map (·.rowCount) == groups.map List.length do
    throw (IO.userError "wrong paired values, nulls, or footer order")
  unless trace.termination == outcome do throw (IO.userError "wrong original indexed cause or EOS")

#eval do
  let group := (List.range 384).map expected
  let .ok ⟨_, source⟩ := openSource limits clean "ordinal" "payload" |
    throw (IO.userError "expected checked paired bindings")
  unless source.groups == [0, 1, 2] do throw (IO.userError "wrong original group ordinals")
  verify clean [group, [], group] .eos
  verify damaged [group, []]
    (.readError (.byteArray (.page 2 1 "payload" 19 21009 (.decode (.plain (.plain .integerOverflow))))))
  unless damaged.data[10937]! == 0 do throw (IO.userError "wrong final-group INT32 tag byte")
  verify ⟨damaged.data.set! 10937 6⟩ [group, []]
    (.readError (.int32 (.page 2 0 "ordinal" 0 10924 (.encoding 3))))
  let .error (.openFailure (.fileRowLimit 767 768)) :=
    readAll { file := { maxFileRows := 767 } } damaged "ordinal" "payload" |
    throw (IO.userError "file cap did not precede the group read")
  IO.println "Legacy mixed events: [384, 0, 384] exact pairs, [384, 0] before either original column error"

end Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy
