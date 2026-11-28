module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.ByteArrayFallback.File.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.ByteArrayFallback.File.Defs

namespace Silmaril.Formats.Parquet.ByteArrayFallback.File

open Silmaril.Formats.Arrow

private def original : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-byte-array-legacy-fallback/parquet-java-v1-legacy-fallback.parquet"⟩
private def clean : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-byte-array-legacy-events/legacy-v1-empty-middle.parquet"⟩
private def damaged : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-byte-array-legacy-events/legacy-v1-late-error.parquet"⟩

private def limits : Limits := { file := { maxFileRows := 768 } }

private def verify (input : Bytes) (expected : List (List (Option Bytes))) (outcome : Events.Termination Error) :
    IO Unit := do
  let .ok ⟨selected, trace⟩ := readAllLegacy limits input "payload" |
    throw (IO.userError "legacy event open rejected")
  unless List.ofFn selected.kind == [("payload", .optional)] do
    throw (IO.userError "wrong selected name or layout")
  let observed := trace.batches.map fun batch =>
    batch.toRows.map fun row => List.ofFn fun index => row index
  unless observed == expected.map (List.map fun slot => [slot]) &&
      trace.batches.map (·.rowCount) == expected.map List.length do
    throw (IO.userError "wrong slots or original group boundaries")
  unless trace.termination == outcome do throw (IO.userError "wrong EOS or indexed error")

#eval do
  let .ok checked := ByteArrayFallback.openFile {} original "payload" |
    throw (IO.userError "producer input rejected")
  let .ok group := ByteArrayFallback.readLegacyGroup checked {} 0 |
    throw (IO.userError "producer group rejected")
  let .ok ⟨_, source⟩ := openLegacySource limits clean "payload" |
    throw (IO.userError "empty-middle fixture rejected")
  unless source.groups == [0, 1, 2] && group.length == 384 do
    throw (IO.userError "wrong original footer positions")
  verify clean [group, [], group] .eos
  verify damaged [group, []]
    (.readError (.readFailure (.page 2 1 "payload" 19 21009 (.decode (.plain (.plain .integerOverflow))))))
  let .error (.openFailure (.fileRowLimit 767 768)) :=
      readAllLegacy { file := { maxFileRows := 767 } } damaged "payload" |
    throw (IO.userError "total row cap did not precede late damage")
  let .ok ⟨_, trace⟩ := readAll limits clean "payload" |
    throw (IO.userError "default source structural open differed")
  let refused : Events.Termination Error := .readError (.readFailure (.column 0 1 "payload" .encodings))
  unless trace.batches.isEmpty && trace.termination == refused do
    throw (IO.userError "default source admitted legacy encodings")
  IO.println "Legacy events: [384, 0, 384] at EOS and [384, 0] before the original group 2, frame 19 failure"

end Silmaril.Formats.Parquet.ByteArrayFallback.File
