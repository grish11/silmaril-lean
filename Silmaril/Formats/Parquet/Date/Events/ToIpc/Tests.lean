module

meta import Silmaril.Formats.Parquet.Date.Events.ToIpc.Defs

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Relational
open Silmaril.Formats.Parquet.Date.Events.ToIpc

private meta def schema (nullable : Bool) : Scan.Schema String Date.Events.Kind :=
  ⟨1, fun _ => ("日付", .date32 nullable)⟩

private meta def events (nullable : Bool) (batches : List Arrow.DateStream.Writer.Column)
    (termination : Arrow.Events.Termination Date.Events.Error := .eos) : Source :=
  .ok ⟨schema nullable,
    ⟨batches.map (fun slots => AlignedColumns.ofRows (slots.map fun slot _ => slot)), termination⟩⟩

private meta def observes (nullable : Bool) (batches : List Arrow.DateStream.Writer.Column) :
    Bool :=
  match emit {} (events nullable batches) with
  | .error _ => false
  | .ok wire =>
    match Arrow.DateStream.read {} wire with
    | .error _ => false
    | .ok decoded => decoded == Arrow.DateStream.Writer.observation "日付" nullable batches

#guard observes true [[some (-2147483648), none], [], [some 2147483647]]
#guard observes false [[some (-1)], [], [some 0]]
#guard observes false []

private meta def rejects (limits : Arrow.ObservationLimits) (source : Source) (expected : Error) :
    Bool :=
  match emit limits source with
  | .error cause => cause == expected
  | .ok _ => false

#guard rejects {} (events false [[some (-1)], [], [none]])
  (.writer (.record 2 (.malformed .batchLayout)))
#guard rejects {} (events true [[some (-1)]] .closed) .closed
#guard rejects {} (events true [[some (-1)]] (.closeError (.groupFailure 1 (.scan .crcUnsupported))))
  (.source (.groupFailure 1 (.scan .crcUnsupported)))
#guard rejects { ipc := { batches := 0 } }
  (events true [[some (-1)]] (.readError (.groupFailure 1 (.scan .unsupportedPageEncoding))))
  (.source (.groupFailure 1 (.scan .unsupportedPageEncoding)))
