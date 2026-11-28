module

public import Silmaril.Formats.Arrow.MixedFlat.Defs
public import Silmaril.Formats.Arrow.Events.Defs

/-! Aligned Arrow event observations shared by mixed IPC readers. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.Events

open Silmaril.Relational

inductive Cell where
  | primitive (value : Arrow.Value)
  | binaryView (value : KBytes)
  | utf8View (value : String)

/-- BinaryView cells retain their checked source octets as kernel bytes. -/
def cells : MixedFlat.Column → List (Option Cell)
  | .primitive values => values.map (Option.map Cell.primitive)
  | .binaryView values => values.map (Option.map Cell.binaryView)
  | .utf8View values => values.map (Option.map Cell.utf8View)

/-- The label is the exact footer declaration. The value carrier distinguishes
the primitive, binary-view and text-view cases. -/
def schema (fields : List MixedFlat.Field) : Scan.Schema MixedFlat.Field Unit :=
  ⟨fields.length, fun i => (fields[i], ())⟩

abbrev Batch (source : Scan.Schema MixedFlat.Field Unit) := Arrow.Events.Batch source (fun _ => Cell)

/-- Exact row count and positional agreement with the decoder observation. -/
def Agrees (source : Scan.Schema MixedFlat.Field Unit) (observed : MixedFlat.Observed)
    (event : Batch source) : Prop :=
  observed.rowCount = event.rowCount ∧ observed.columns.length = source.width ∧
    ∀ i : Fin source.width,
      observed.columns[i.val]?.map (fun pair => (pair.1, cells pair.2)) =
        some ((source.kind i).1, event.values i)

/-- Form one aligned event without changing its row count or slot order. -/
def ofObserved (fields : List MixedFlat.Field) (observed : MixedFlat.Observed)
    (ordered : observed.columns.map Prod.fst = fields)
    (aligned : ∀ pair ∈ observed.columns, (cells pair.2).length = observed.rowCount) :
    Batch (schema fields) :=
  have width : observed.columns.length = fields.length := by
    simpa using congrArg List.length ordered
  let columns := (observed.columns.toArray).map (fun pair => cells pair.2)
  have size : columns.size = fields.length := by simpa [columns] using width
  ⟨observed.rowCount, fun i => columns[i.val]'(Nat.lt_of_lt_of_eq i.isLt size.symm), by
    intro i
    simp [columns]
    exact aligned _ (List.getElem_mem _)⟩

end Silmaril.Formats.Arrow.MixedFlat.Events
