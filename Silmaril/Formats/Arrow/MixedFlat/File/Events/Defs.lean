module

public import Silmaril.Formats.Arrow.MixedFlat.File.Defs
public import Silmaril.Formats.Arrow.Events.Defs
import Silmaril.Proofs.Formats.Arrow.MixedFlat.File.Events.Shape

/-! Eager conversion of a checked mixed IPC file to an Arrow event trace. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.File.Events

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

inductive Error where
  | file (cause : MixedFlat.File.Error)
  | budget (batch : Nat) (cause : Arrow.Error)
  deriving DecidableEq, Repr

abbrev Batch (source : Scan.Schema MixedFlat.Field Unit) := Arrow.Events.Batch source (fun _ => Cell)
abbrev Trace (source : Scan.Schema MixedFlat.Field Unit) := Arrow.Events.Trace source (fun _ => Cell) Error
abbrev Stream := Arrow.Events.EventStream MixedFlat.Field (fun _ : Unit => Cell) Error

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

/-- Eager decoding returns the entire trace with EOS, or an atomic error.
The original decoder checks each candidate batch before the running row
and cell budgets are checked, so at most one candidate is decoded beyond
the accumulated observation budget. -/
def read (limits : MixedFlat.Limits) (input : KBytes) : Stream :=
  (do
    let index ← (MixedFlat.File.readIndex limits.observation.ipc input).mapError Error.file
    let batches ← drain limits input index.footer.fields 0 0 index.footer.blocks
    return ⟨schema index.footer.fields, ⟨batches, .eos⟩⟩ :
    Except Error (Σ signature : Scan.Schema MixedFlat.Field Unit, Trace signature))
where
  drain (limits : MixedFlat.Limits) (input : KBytes) (fields : List MixedFlat.Field) :
      Nat → Nat → List FileBlock → Except Error (List (Batch (schema fields)))
    | _, _, [] => .ok []
    | n, rows, block :: rest =>
      match parsed : MixedFlat.File.readRecord limits input fields block with
      | .error cause => .error (.file (.batch n cause))
      | .ok observed => do
        let total := rows + observed.rowCount
        (Body.checkBudget limits.observation fields.length total).mapError (.budget n)
        let remaining ← drain limits input fields (n + 1) total rest
        let batch := ofObserved fields observed
          (by exact (Proofs.Formats.Arrow.MixedFlat.File.Events.readRecord_shape parsed).1)
          (by
            intro pair member
            have slots := (Proofs.Formats.Arrow.MixedFlat.File.Events.readRecord_shape parsed).2 pair member
            cases column : pair.2 <;>
              simpa [column, cells, Proofs.Formats.Arrow.MixedFlat.File.Events.slotCount] using slots)
        return batch :: remaining

end Silmaril.Formats.Arrow.MixedFlat.File.Events
