module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.ByteArrayFallback.File.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.ByteArrayFallback.File.Defs

/-! Exact selected batches and original indexed errors from pinned inputs. -/

namespace Silmaril.Formats.Parquet.ByteArrayFallback.File

open Silmaril.Formats.Arrow

private def v1 : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-byte-array-fallback/byte-array-fallback-v1.parquet"⟩
private def v2 : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-byte-array-fallback/byte-array-fallback-v2.parquet"⟩
private def missingDictionary : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-byte-array-fallback/byte-array-fallback-v2-missing-dictionary.parquet"⟩
private def badTag : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-byte-array-fallback/byte-array-fallback-v2-bad-tag.parquet"⟩
private def badLength : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-byte-array-fallback/byte-array-fallback-v2-bad-length.parquet"⟩
private def emptyMiddle : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-int32-byte-array-file/empty-middle-v2.parquet"⟩

private def verify (input : Bytes) (limits : Limits) (expected : List (List (Option Bytes)))
    (outcome : Events.Termination Error) : IO Unit := do
  let .ok ⟨selected, trace⟩ := readAll limits input "payload" |
    throw (IO.userError "file rejected at open")
  unless List.ofFn selected.kind == [("payload", .optional)] do
    throw (IO.userError "wrong selected field")
  let observed := trace.batches.map fun batch =>
    batch.toRows.map fun row => List.ofFn fun index => row index
  unless observed == expected.map (List.map fun value => [value]) &&
      trace.batches.map (·.rowCount) == expected.map List.length do
    throw (IO.userError "wrong slots or footer group boundaries")
  unless trace.termination == outcome do throw (IO.userError "wrong EOS or original indexed failure")

private def checkedFile (input : Bytes) : IO (Checked "payload") := do
  let .ok checked := ByteArrayFallback.openFile {} input "payload" |
    throw (IO.userError "fallback input rejected at open")
  return checked

private def clean (label : String) (input : Bytes) : IO Unit := do
  let checked ← checkedFile input
  let indices := (source checked {}).groups
  unless indices == [0, 1] do throw (IO.userError "original footer ordinals differ")
  let .ok groups := indices.mapM (ByteArrayFallback.readGroup checked {}) |
    throw (IO.userError "expected successful original group reads")
  unless groups.map List.length == [384, 384] do throw (IO.userError "wrong source group counts")
  verify input {} groups .eos
  IO.println s!"{label}: [384, 384] exact opaque slots in original footer order"

#eval clean "V1" v1
#eval clean "V2" v2

private def damaged (input : Bytes) (page offset : Nat)
    (reason : FlatColumn.PageError DecodeError) : IO Unit := do
  let checked ← checkedFile v2
  let .ok first := ByteArrayFallback.readGroup checked {} 0 |
    throw (IO.userError "expected reference group zero")
  verify input { file := { maxFileRows := 768 } } [first]
    (.readError (.readFailure (.page 1 1 "payload" page offset reason)))
  let .error (.openFailure (.fileRowLimit 767 768)) :=
    readAll { file := { maxFileRows := 767 } } input "payload" |
    throw (IO.userError "expected total row cap before group reads")
  IO.println s!"V2 prefix [384] then group 1, column 1, frame {page}, header {offset}"

#eval damaged missingDictionary 0 15111 (.decode .missingDictionary)
#eval damaged badTag 19 16814 (.encoding 3)
#eval damaged badLength 24 22513 (.decode (.plain (.plain .integerOverflow)))

#eval do
  let expected : List (List (Option Bytes)) :=
    [[none, some .empty, some (Bytes.ofList [0xFF, 0])], [],
      [some (Bytes.ofList [0x80]), some (Bytes.ofList [120, 121])]]
  let limits : Limits := { file := { maxFileRows := 5 } }
  verify emptyMiddle limits expected .eos
  unless emptyMiddle.data[122]! == 0 do throw (IO.userError "wrong final value encoding byte")
  verify ⟨emptyMiddle.data.set! 122 6⟩ limits (expected.take 2)
    (.readError (.readFailure (.page 2 1 "payload" 0 108 (.encoding 3))))
  IO.println "Admitted empty group: [3, 0, 2] at EOS and [3, 0] before the original group 2 failure"

end Silmaril.Formats.Parquet.ByteArrayFallback.File
