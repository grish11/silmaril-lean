module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.FlatColumn.Window.Thms
meta import Batteries.Data.Except
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.FlatColumn.Window.Defs

/-! Independent V1 PLAIN fixtures and typed precedence controls for late corruption. -/

namespace Silmaril.Formats.Parquet.FlatColumn.Window

private def indexed : Bytes := ⟨include_bytes "../../../../../data/parquet-offset-index/v1-index.parquet"⟩
private def unindexed : Bytes := ⟨include_bytes "../../../../../data/parquet-offset-index/v1-no-index.parquet"⟩

private inductive DecodeError where
  | kind
  | scalar (reason : ScalarPage.Error)
  deriving DecidableEq, Repr

private def decodePlain : DecodePage Int32 DecodeError := fun _ metadata header body => do
  let some params := pageParameters .optional metadata.codec header | throw .kind
  (ScalarPage.decode .int32 params ⟨1024, 1024, ⟨16, 128⟩, 0⟩ body).mapError .scalar

private abbrev PlanObservation := Except OffsetIndex.Error (Option (List (Nat × Nat × Nat)))

private structure Observation where
  rows : List (Option Int32)
  indexPlan : PlanObservation
  deriving DecidableEq

private def observed (source : Bytes) (first stop : Nat)
    (limits : Limits := {}) (indexLimits : OffsetIndex.Limits := {}) :
    Option (Except (Error DecodeError) Observation) := do
  let snapshot ← (Snapshot.check (Failure := Unit) {} source).toOption
  let binding ← (bindColumn snapshot ⟨"number", .int32, .optional⟩).toOption
  pure ((Window.read binding limits { encoding := 0 } decodePlain indexLimits 1 first stop).map fun result =>
    ⟨result.rows, result.indexPlan.map (Option.map (List.map fun clip =>
      (clip.page.frame.header.start, clip.localBounds.1, clip.localBounds.2)))⟩)

private def expectedRows : List (Option Int32) :=
  [none, some 29, some 32, some 35, some 38, none, some 44]

private def expectedPlan : PlanObservation := .ok (some [(109, 3, 4), (144, 0, 4), (183, 0, 2)])

#guard observed indexed 3 10 = some (.ok ⟨expectedRows, expectedPlan⟩)
#guard observed indexed 10 15 = some (.ok ⟨[some 47, some 50], .ok (some [(183, 2, 4)])⟩)
#guard observed indexed 0 0 = some (.ok ⟨[], .ok (some [])⟩)
#guard observed indexed 8 4 = some (.ok ⟨[], .ok (some [])⟩)
#guard observed unindexed 3 10 = some (.ok ⟨expectedRows, .ok none⟩)

-- The selected reader's framing cap supplies the framing for both walks.
#guard observed indexed 3 10 (indexLimits := { page := { maxPages := 0 } }) =
  some (.ok ⟨expectedRows, expectedPlan⟩)
#guard observed indexed 3 10 (indexLimits := { maxIndexBytes := 26 }) =
  some (.ok ⟨expectedRows, .error .indexByteLimit⟩)
#guard observed indexed 0 0 (limits := { maxRows := 11 }) =
  some (.error (.column 1 0 "number" (.rowLimit 11 12)))

private def badIndex : Bytes := ⟨indexed.data.set! 356 0xdc⟩

#guard observed badIndex 3 10 = some (.ok ⟨expectedRows, .error (.pageOffset 0 110 109)⟩)
#guard observed badIndex 0 0 = some (.ok ⟨[], .error (.pageOffset 0 110 109)⟩)

-- Change the length word of the definition section in the third page.
private def badBody : Bytes := ⟨indexed.data.set! 200 0xff⟩
private def badBodyAndIndex : Bytes := ⟨badBody.data.set! 356 0xdc⟩

private def lateError : Error DecodeError :=
  .page 1 0 "number" 2 183 (.decode (.scalar (.levels .definitionByteLimit)))

#guard observed badBody 0 12 = some (.error lateError)
#guard observed badBody 0 4 = some (.error lateError)
#guard observed badBody 3 3 = some (.error lateError)
#guard observed badBodyAndIndex 3 3 = some (.error lateError)

end Silmaril.Formats.Parquet.FlatColumn.Window
