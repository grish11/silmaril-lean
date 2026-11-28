module

meta import Silmaril.Formats.Arrow.DateStream.Writer.Defs
meta import Silmaril.Formats.Parquet.Date.FromIpc.Multi.Defs

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Date.FromIpc.Multi

private meta def limits : Limits :=
  ⟨⟨1, 4096, {}, ⟨{}, 64, ⟨64, 256, ⟨16, 64⟩, 0⟩⟩⟩, 16, 32⟩

private meta def observes (nullable : Bool) (batches : List Arrow.DateStream.Writer.Column) : Bool :=
  ((do
    let source ← (Arrow.DateStream.Writer.emit {} "日付" nullable batches).toOption
    let wire ← (convert {} limits {} source).toOption
    let checked ← (Date.openChecked {} wire).toOption
    let groups ← (Internal.readGroups {} checked).toOption
    return checked.snapshot.groupCount == batches.length &&
      checked.snapshot.metadata.numRows == Int.ofNat (batches.map List.length).sum &&
      checked.binding.leaf == Date.FromIpc.leaf ⟨"日付", nullable, .day⟩ &&
      checked.binding.annotation == .logicalAndConverted &&
      groups.map (·.date32Slots) == batches &&
      groups.map (·.rowCount) == batches.map List.length
    : Option Bool)).getD false

#guard observes true [[some (-2147483648), none], [], [some 2147483647]]
#guard observes false [[], [some (-1), some 0], []]
#guard observes true [[], [], []]

private meta def rejects (writer : Limits) (reader : Date.Limits)
    (batches : List Arrow.DateStream.Writer.Column) (expected : Error) : Bool :=
  match Arrow.DateStream.Writer.emit {} "date" true batches with
  | .error _ => false
  | .ok source =>
    match convert {} writer reader source with
    | .error actual => actual == expected
    | .ok _ => false

#guard rejects limits {} [] (.source (.batchCount 0))
#guard rejects { limits with maxGroups := 2 } {} [[], [], []] .groupLimit
#guard rejects { limits with writer.footer.compact.maxCollectionSize := 2 } {}
  [[], [], []] .groupLimit
#guard rejects { limits with maxTotalRows := 2 } {} [[none, some (-1)], [], [some 0]] .totalRows
#guard rejects { limits with writer.maxFileBytes := 11 } {} [[]] .fileLimit
#guard rejects { limits with writer.footer.maxFooterBytes := 0 } {} [[]] (.footer .byteLimit)
#guard rejects limits { scan := { maxRows := 1 } } [[none], [], [some 0, some 1]]
  (.groupReadback 2 (.scan .rowLimit))

#guard match Arrow.DateStream.Writer.emit {} "date" true [[none], [], [some 0]] with
  | .error _ => false
  | .ok source =>
    let truncated := source.slice 0 (source.len - 8)
    match convert {} { limits with maxGroups := 0 } {} truncated with
    | .error actual => actual == .source (.reader (.batch 3 (.envelope (.malformed .truncated))))
    | .ok _ => false

private meta def agreesWithSingle (nullable : Bool) (words : Arrow.DateStream.Writer.Column) : Bool :=
  match Arrow.DateStream.Writer.emit {} "date" nullable [words] with
  | .error _ => false
  | .ok source =>
    match convert {} limits {} source, Date.FromIpc.convert {} limits.writer {} source with
    | .ok multi, .ok single => multi == single
    | _, _ => false

#guard agreesWithSingle true [some (-1), none, some 0]
#guard agreesWithSingle false []
