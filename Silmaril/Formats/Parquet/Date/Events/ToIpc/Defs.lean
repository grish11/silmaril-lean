module

public import Silmaril.Formats.Parquet.Date.Events.Defs
public import Silmaril.Formats.Arrow.DateStream.Writer.Defs

/-! # Checked Parquet DATE events to complete Arrow Date32 IPC streams -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.Events.ToIpc

open Silmaril.Relational

abbrev Source := Arrow.Events.EventStream String Cell Date.Events.Error

inductive Error where
  | source (cause : Date.Events.Error)
  | closed
  | fieldCount (actual : Nat)
  | writer (cause : Arrow.DateStream.Writer.Error)
  deriving DecidableEq, Repr

/-- Preserve the typed column of each batch, including empty batches. -/
def batchSlots {schema : Scan.Schema String Kind}
    (trace : Arrow.Events.Trace schema Cell Date.Events.Error) (column : Fin schema.width) :
    List Arrow.DateStream.Writer.Column :=
  trace.batches.map fun batch => batch.values column

/-- An original source error takes precedence over writer checks. Only an
EOS-terminated trace can produce a complete Date32 IPC stream. -/
def emit (limits : Arrow.ObservationLimits) (source : Source) : Except Error KBytes :=
  match source with
  | .error cause => .error (.source cause)
  | .ok ⟨schema, trace⟩ =>
    match trace.termination with
    | .readError cause | .closeError cause => .error (.source cause)
    | .closed => .error .closed
    | .eos =>
      if one : schema.width = 1 then
        let column : Fin schema.width := ⟨0, by omega⟩
        match schema.kind column with
        | (name, .date32 nullable) =>
          (Arrow.DateStream.Writer.emit limits name nullable (batchSlots trace column)).mapError .writer
      else .error (.fieldCount schema.width)

/-- Decode through the existing checked DATE event source, then emit native
Date32 IPC bytes from its complete ordered batches. -/
def convert (inputLimits : Date.Limits) (outputLimits : Arrow.ObservationLimits)
    (input : Bytes) : Except Error KBytes :=
  emit outputLimits (Date.Events.readAll inputLimits input)

end Silmaril.Formats.Parquet.Date.Events.ToIpc
