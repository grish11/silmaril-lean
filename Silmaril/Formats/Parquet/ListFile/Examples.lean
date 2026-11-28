module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.ListFile.Thms
meta import Batteries.Data.Except
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.ListFile.Defs
meta import Silmaril.Formats.Arrow.Events.Defs

namespace Silmaril.Formats.Parquet.ListFile

open Silmaril.Formats.Arrow.Events

private def fixture : Bytes :=
  ⟨include_bytes "../../../../data/parquet-list-file/nullable-int32-v1.parquet"⟩

private def snappy : Bytes :=
  ⟨include_bytes "../../../../data/parquet-list-file/nullable-int32-v1-snappy.parquet"⟩

private def first : List ListPage.Row :=
  [none, some [], some [none], some [some (-7), none, some 0], some [some 9, none]]

private def second : List ListPage.Row :=
  [some [some 10, none], none, some [], some [none, some (-2147483648)], some [some 2147483647, none]]

private def change (source : Bytes) (offset : Nat) (value : UInt8) : Bytes :=
  Bytes.ofList (source.toList.set offset value)

private def observe (source : Bytes) :
    Except Error (String × Kind × List (Nat × List ListPage.Row) × Termination Error) := do
  let ⟨schema, trace⟩ ← readAll {} source
  if bound : 0 < schema.width then
    let field : Fin schema.width := ⟨0, bound⟩
    let (name, kind) := schema.kind field
    pure (name, kind, trace.batches.map (fun batch => (batch.rowCount, batch.values field)),
      trace.termination)
  else
    -- Always a one-column schema in this adapter.
    pure ("", .nullableListOfNullableInt32, [], trace.termination)


set_option synthInstance.maxSize 4096

#guard observe fixture = .ok ("samples", .nullableListOfNullableInt32, [(5, first), (5, second)], .eos)

-- The original first batch survives the second frame's leading continuation.
#guard observe (change fixture 72 0xa3) = .ok
  ("samples", .nullableListOfNullableInt32, [(5, first)],
    .readError (.groupFailure 1 (.page .continuationWithoutList)))

#guard observe (change fixture 56 18) = .ok
  ("samples", .nullableListOfNullableInt32, [(5, first)],
    .readError (.groupFailure 1 (.slotCount 8 9)))

-- The unchanged path and converted LIST code are insufficient to admit a different modern arm.
#guard observe (change fixture 125 0x4c) = .error (.openFailure .invalidList)
#guard observe (change fixture 123 0x08) = .error (.openFailure .invalidList)
#guard observe (change fixture 173 0x69) = .error (.openFailure (.snapshot (.invalidMetadata .columns)))
#guard observe snappy = .ok
  ("samples", .nullableListOfNullableInt32, [], .readError (.groupFailure 0 (.codec 1)))
#guard (openFile { maxFileBytes := 48 } fixture).map (fun _ => ()) = .error .fileLimit
#guard (openFile {} fixture).toOption.map (·.readGroup 2) = some (.error (.groupOrdinal 2))
#guard (openFile { page := { maxRows := 4 } } fixture).toOption.map (·.readGroup 0) =
  some (.error (.page .rowLimit))

end Silmaril.Formats.Parquet.ListFile
