module

import Silmaril.Formats.Parquet.FlatInt32Writer.Readback.Arrow.Defs
meta import Silmaril.Formats.Parquet.FlatInt32Writer.Readback.Arrow.Defs

/-! Project Arrow events from the checked byte snapshot of an emitted file. -/

namespace Silmaril.Formats.Parquet.FlatInt32Writer

open Silmaril.Relational Silmaril.Formats.Arrow

private def limits : Limits := ⟨16, 4096, {}, ⟨{}, 32, ⟨64, 64, ⟨16, 32⟩, 0⟩⟩⟩

private def mixed : Input :=
  ⟨3, [⟨"id", .required [-2147483648, 0, 2147483647]⟩,
    ⟨"café", .optional [some 7, none, some (-4)]⟩,
    ⟨"nulls", .optional [none, none, none]⟩]⟩

private def empty : Input :=
  ⟨0, [⟨"id", .required []⟩, ⟨"café", .optional []⟩, ⟨"nulls", .optional []⟩]⟩

private def readProjected (input : Input) (indices : List Nat)
    (keep : (schema : Scan.Schema String Unit) → Scan.Predicate schema Snapshot.FlatInt32.Cell :=
      fun _ _ => some true) :
    Option (List String × Nat × List (List (Option Int32))) := do
  let file ← (emit limits input).toOption
  let ⟨actual, trace⟩ ← (Snapshot.FlatInt32.readAll (limits.snapshotLimits input) input.arrowSchema
    file.bytes).toOption
  let checked ← indices.mapM fun index =>
    if bound : index < actual.width then some (⟨index, bound⟩ : Fin actual.width) else none
  let projected := trace.scan (Scan.Projection.ofArray checked.toArray) (keep actual)
  let result := projected.collect
  let .eos := result.termination | none
  let [batch] := projected.batches | none
  if batch.rowCount != result.table.rowCount then none else
    return (List.ofFn fun index => (result.table.schema.kind index).1,
      result.table.rowCount, projected.rows.map List.ofFn)

#guard decide (readProjected mixed [1, 0, 1] = some (["café", "id", "café"], 3,
  [[some 7, some (-2147483648), some 7], [none, some 0, none], [some (-4), some 2147483647, some (-4)]]))
#guard decide (readProjected mixed [] = some ([], 3, [[], [], []]))
#guard decide (readProjected empty [1, 0, 1] = some (["café", "id", "café"], 0, []))
#guard decide (readProjected empty [] = some ([], 0, []))

private def keepPresent (schema : Scan.Schema String Unit) : Scan.Predicate schema Snapshot.FlatInt32.Cell :=
  fun row => if inRange : 1 < schema.width then (row ⟨1, inRange⟩).map (fun _ => true) else none

#guard decide (readProjected mixed [1, 0, 1] keepPresent = some (["café", "id", "café"], 2,
  [[some 7, some (-2147483648), some 7], [some (-4), some 2147483647, some (-4)]]))
#guard decide (readProjected mixed [] keepPresent = some ([], 2, [[], []]))

end Silmaril.Formats.Parquet.FlatInt32Writer
