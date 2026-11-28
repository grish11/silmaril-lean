module

meta import Silmaril.Formats.Arrow.DateStream.Writer.Defs
meta import Silmaril.Formats.Parquet.Date.FromIpc.Defs

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Date.FromIpc

private meta def writerLimits : FlatInt32Writer.Limits :=
  ⟨1, 4096, {}, ⟨{}, 64, ⟨64, 256, ⟨16, 64⟩, 0⟩⟩⟩

private meta def observes (name : String) (nullable : Bool) (days : List (Option Int32)) : Bool :=
  ((do
    let source ← (Arrow.DateStream.Writer.emit {} name nullable [days]).toOption
    let wire ← (convert {} writerLimits {} source).toOption
    let checked ← (Date.openChecked {} wire).toOption
    let group ← (checked.readGroup {} 0).toOption
    return checked.snapshot.groupCount == 1 &&
      group.binding.leaf == leaf ⟨name, nullable, .day⟩ &&
      group.binding.annotation == .logicalAndConverted &&
      group.rowCount == days.length && group.date32Slots == days &&
      (match checked.readGroup {} 1 with | .error (.groupIndex 1) => true | _ => false)
    : Option Bool)).getD false

#guard observes "日付" true [some (-2147483648), none, some (-1), some 0, some 11016, some 2147483647]
#guard observes "époque" false [some (-719528), some 0, some 11016]
#guard observes "required-empty" false []
#guard observes "optional-empty" true []

private meta def rejects (limits : FlatInt32Writer.Limits)
    (batches : List Arrow.DateStream.Writer.Column) (expected : Error) : Bool :=
  match Arrow.DateStream.Writer.emit {} "date" true batches with
  | .error _ => false
  | .ok source =>
    match convert {} limits {} source with
    | .ok _ => false
    | .error actual => actual == expected

#guard rejects writerLimits [] (.batchCount 0)
#guard rejects writerLimits [[], []] (.batchCount 2)
#guard rejects { writerLimits with maxFileBytes := 0 } [[none]] (.writer .fileLimit)

#guard match Arrow.DateStream.Writer.emit {} "date" false [[some (-1)]] with
  | .error _ => false
  | .ok source =>
    let truncated := source.slice 0 (source.len - 8)
    match convert {} { writerLimits with maxFileBytes := 0 } {} truncated with
    | .error actual => actual == .reader (.batch 1 (.envelope (.malformed .truncated)))
    | .ok _ => false

#guard match Arrow.DateStream.Writer.emit {} "date" false [[some (-1)]] with
  | .error _ => false
  | .ok source =>
    match convert {} writerLimits { scan := { maxRows := 0 } } source with
    | .error actual => actual == .readback (.scan .rowLimit)
    | .ok _ => false
