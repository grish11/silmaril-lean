module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.ListFile.Multi.Thms
meta import Batteries.Data.Except
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.ListFile.Multi.Defs
meta import Silmaril.Formats.Arrow.Events.Defs

namespace Silmaril.Formats.Parquet.ListFile.Multi

open Silmaril.Formats.Arrow.Events

private def native : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-list-continuation/native-v1.parquet"⟩

private def continued : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-list-continuation/authored-continuation-v1.parquet"⟩

private def indexed : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-list-continuation/native-indexed-v1.parquet"⟩

private def prior : Bytes := ⟨include_bytes "../../../../../data/parquet-list-file/nullable-int32-v1.parquet"⟩

private def change (source : Bytes) (offset : Nat) (value : UInt8) : Bytes :=
  Bytes.ofList (source.toList.set offset value)

private def read (source : Bytes) (limits : Limits := {}) :
    Option (Except GroupError (List ListPage.Row)) :=
  (ListFile.openFile limits.file source).toOption.map (fun checked => readGroup limits.maxGroupSlots checked 0)

private def observe (source : Bytes) :
    Except Error (List (List ListPage.Row) × Termination Error) := do
  let ⟨schema, trace⟩ ← readAll {} source
  let some field := (List.finRange schema.width).head? | pure ([], trace.termination)
  pure (trace.batches.map (·.values field), trace.termination)

private def originalRows : List ListPage.Row :=
  [none, some [], some [some 11, none], some [some 22, none]]

private def continuedRows : List ListPage.Row :=
  [none, some [], some [some 11, none, some 22, none]]

set_option synthInstance.maxSize 1024

#guard observe native = .ok ([originalRows], .eos)
#guard observe continued = .ok ([continuedRows], .eos)
#guard observe indexed = .ok ([originalRows], .eos)

-- Both refusals have syntactically valid level/value pairs.
#guard read (change (change native 28 1) 34 2) =
  some (.error (.frame 0 4 (.page .continuationWithoutList)))
#guard read (change native 90 3) =
  some (.error (.frame 2 66 (.page .continuationWithoutList)))
#guard read (change indexed 118 3) = some (.error (.frame 3 96 .indexedContinuation))

#guard read (change native 126 3) = some (.error (.rowCount 4 3))
#guard read (change native 237 10) = some (.error (.frame 3 102 (.slotBudget 1 2)))
#guard read (change native 237 14) = some (.error (.missingSlots 1))
#guard read native { maxGroupSlots := 5 } = some (.error .slotLimit)
#guard read native { file.page.maxRows := 3 } = some (.error .rowLimit)
#guard read native { file.framing.maxPages := 3 } = some (.error (.framing (.framing .pageLimit)))

-- The original singleton entry point retains its page-count policy.
#guard (ListFile.openFile {} native).toOption.map (·.readGroup 0) = some (.error .pageCount)

#guard observe (change prior 72 0xa3) = .ok
  ([[none, some [], some [none], some [some (-7), none, some 0], some [some 9, none]]],
    .readError (.groupFailure 1 (.frame 0 48 (.page .continuationWithoutList))))

end Silmaril.Formats.Parquet.ListFile.Multi
