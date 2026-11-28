module

public import Silmaril.Formats.Arrow.MixedFlat.File.Defs
public import Silmaril.Formats.Arrow.MixedFlat.Events.Defs
import Silmaril.Proofs.Formats.Arrow.MixedFlat.File.Events.Shape

/-! Eager conversion of a checked mixed IPC file to an Arrow event trace. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.File.Events

open Silmaril.Relational

export MixedFlat.Events (Cell cells schema Batch Agrees ofObserved)

namespace Cell
export MixedFlat.Events.Cell (primitive binaryView utf8View)
end Cell

inductive Error where
  | file (cause : MixedFlat.File.Error)
  | budget (batch : Nat) (cause : Arrow.Error)
  deriving DecidableEq, Repr

abbrev Trace (source : Scan.Schema MixedFlat.Field Unit) := Arrow.Events.Trace source (fun _ => Cell) Error
abbrev Stream := Arrow.Events.EventStream MixedFlat.Field (fun _ : Unit => Cell) Error

/-- Decode one strict record, check its running observation budget, and
form the aligned event used by both eager and pull readers. -/
def readStep (limits : MixedFlat.Limits) (input : KBytes) (fields : List MixedFlat.Field)
    (n rows : Nat) (block : FileBlock) : Except Error (Nat × Batch (schema fields)) :=
  match parsed : MixedFlat.File.readRecord limits input fields block with
  | .error cause => .error (.file (.batch n cause))
  | .ok observed => do
    let total := rows + observed.rowCount
    (Body.checkBudget limits.observation fields.length total).mapError (.budget n)
    let batch := ofObserved fields observed
      (by exact (Proofs.Formats.Arrow.MixedFlat.File.Events.readRecord_shape parsed).1)
      (by exact (Proofs.Formats.Arrow.MixedFlat.File.Events.readRecord_shape parsed).2)
    return (total, batch)

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
    | n, rows, block :: rest => do
      let (total, batch) ← readStep limits input fields n rows block
      return batch :: (← drain limits input fields (n + 1) total rest)

end Silmaril.Formats.Arrow.MixedFlat.File.Events
