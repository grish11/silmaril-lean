module

public import Silmaril.Formats.Arrow.MixedFlat.File.Window.Defs
public import Silmaril.Semantics.Relational.Scan.Defs
import Silmaril.Proofs.Formats.Arrow.MixedFlat.File.Window.Projection.Shape

/-! Positional projection of one fully checked mixed IPC file batch. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.File.Window

open Silmaril.Relational

/-- The positional labels retain each complete Arrow field declaration. -/
def Index.projectionSchema {input : KBytes} {start stop : Nat} (index : Index input start stop) :
    Scan.Schema MixedFlat.Field Unit :=
  ⟨index.footer.fields.length, fun i => (index.footer.fields[i], ())⟩

/-- Check caller-supplied zero-based positions against the footer. Output order
and repetition are permitted, including an empty projection. -/
def Index.checkProjection {input : KBytes} {start stop : Nat} (index : Index input start stop)
    (positions : List Nat) : Option (Scan.Projection index.projectionSchema) := do
  let checked ← positions.mapM fun position =>
    if bound : position < index.footer.fields.length then some ⟨position, bound⟩ else none
  return Scan.Projection.ofArray checked.toArray

/-- Read a single footer entry and project its checked observation. The full
selected batch is validated before selecting columns. An absent entry stays
absent, and a present batch retains its row count even at output width zero. -/
def Index.readProjectedAt {input : KBytes} {start stop : Nat} (index : Index input start stop)
    (limits : MixedFlat.Limits) (n : Nat) (projection : Scan.Projection index.projectionSchema) :
    Except Error (Option MixedFlat.Observed) :=
  match read : index.readAt limits n with
  | .error cause => .error cause
  | .ok none => .ok none
  | .ok (some observed) =>
    let columns := observed.columns.toArray
    have width : columns.size = index.projectionSchema.width := by
      have fields := Proofs.Formats.Arrow.MixedFlat.File.Window.Projection.readAt_fields index read
      simpa [columns, Index.projectionSchema] using congrArg List.length fields
    .ok (some ⟨observed.rowCount, List.ofFn fun output =>
      columns[(projection.index output).val]'(Nat.lt_of_lt_of_eq (projection.index output).isLt width.symm)⟩)

end Silmaril.Formats.Arrow.MixedFlat.File.Window
