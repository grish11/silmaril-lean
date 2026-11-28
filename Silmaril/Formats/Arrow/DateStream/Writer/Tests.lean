module

meta import Silmaril.Formats.Arrow.DateStream.Writer.Defs

open Silmaril Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.DateStream

private meta def observes (name : String) (nullable : Bool) (batches : List (List (Option Int))) :
    Bool :=
  let slots := batches.map (List.map (Option.map Int32.ofInt))
  match Writer.emit {} name nullable slots with
  | .error _ => false
  | .ok wire =>
    match DateStream.read {} wire with
    | .error _ => false
    | .ok stream =>
      stream.field == (⟨name, nullable, .day⟩ : DateStream.Field) &&
        stream.batches.map (List.map (fun slot => slot.bind (·.toEpochDay?))) == batches

#guard observes "日付" true
  [[some (-2147483648), some (-1), none], [], [some 0, some 11016, some 2147483647]]
#guard observes "époque" false [[some (-719528), some (-1)], [some 0]]
#guard observes "日付" false []
#guard observes "日付" false [[]]

private meta def rejects (limits : ObservationLimits) (nullable : Bool)
    (batches : List Writer.Column) (error : Writer.Error) : Bool :=
  match Writer.emit limits "日付" nullable batches with
  | .error actual => actual == error
  | .ok _ => false

#guard rejects {} false [[some (-1)], [], [none]] (.record 2 (.malformed .batchLayout))
#guard rejects { ipc := { batches := 1 } } true [[], []] (.writer (.limit .batches))
#guard rejects { totalRows := 1 } true [[none], [none]] (.writer (.limit .totalRows))
#guard rejects { totalCells := 1 } true [[none], [none]] (.writer (.limit .totalCells))
#guard rejects { ipc := { rows := 1 } } true [[], [none, none]] (.record 1 (.limit .rows))
#guard rejects { ipc := { bodyBytes := 0 } } true [[], [none]] (.record 1 (.limit .bodyBytes))
#guard rejects { ipc := { fields := 0 } } true [] (.writer (.limit .fields))
#guard rejects { ipc := { metadataBytes := 72 } } true [] (.writer (.limit .metadataBytes))
