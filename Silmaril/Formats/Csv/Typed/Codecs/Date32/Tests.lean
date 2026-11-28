module

meta import Silmaril.Formats.Csv.Typed.Codecs.Date32.Defs
meta import Silmaril.Formats.Parquet.Date.Events.Defs

open Silmaril.Formats
open Silmaril.Formats.Csv.Typed.Codecs.Date32
open Silmaril.Formats.Parquet.Date.Events (Kind)

private meta def bytes (text : String) : Csv.Bytes := text.toUTF8.data.toList

private meta def nullable : Kind → Bool
  | .date32 allowsNull => allowsNull

private meta def schema (allowsNull : Bool) : Csv.Typed.Schema Kind :=
  ⟨1, fun _ => (bytes "日付", .date32 allowsNull)⟩

private meta def slots {schema : Csv.Typed.Schema Kind} (table : Csv.Typed.Table schema Cell)
    (first : Fin schema.width) : List (Option Int) :=
  table.map fun row => (row first).map Int32.toInt

private meta def checksCell (day : Int) (text : String) : Bool :=
  let word := Int32.ofInt day
  print word == some (bytes text) && parse (bytes text) == some word

private meta def rejectsWire (wire : Csv.Bytes) (allowsNull : Bool) (cause : Error) : Bool :=
  match decode (schema allowsNull) nullable wire with
  | .error actual => actual == cause
  | .ok _ => false

-- The external oracle supplies the pinned PyArrow file and CPython CSV bytes.
private meta def checksCollected (input : Bytes) (quoted minimal : Csv.Bytes)
    (expected : List (Option Int)) : Bool := Id.run do
  let stream := Parquet.Date.Events.readAll {} input
  let .ok ⟨_, trace⟩ := stream | return false
  if trace.batches.map (·.rowCount) != [5, 4] then return false
  let .ok observed := stream.collect | return false
  let .eos := observed.termination | return false
  let source := observed.table.schema
  if h : source.width = 1 then
    let first : Fin source.width := ⟨0, by omega⟩
    if source.kind first != ("日付", .date32 true) then return false
    let target : Csv.Typed.Schema Kind :=
      ⟨source.width, fun i => let (label, kind) := source.kind i; (bytes label, kind)⟩
    let table : Csv.Typed.Table target Cell := observed.table.rows
    if slots table first != expected then return false
    let .ok written := encode target nullable table | return false
    if written != quoted then return false
    let .ok fromQuoted := decode target nullable quoted | return false
    let .ok fromMinimal := decode target nullable minimal | return false
    return slots fromQuoted first == expected && slots fromMinimal first == expected
  else return false

#guard checksCell (-719528) "0000-01-01"
#guard checksCell (-719469) "0000-02-29"
#guard checksCell (-1) "1969-12-31"
#guard checksCell 0 "1970-01-01"
#guard checksCell 11016 "2000-02-29"
#guard checksCell 2932896 "9999-12-31"
#guard [-2147483648, -719529, 2932897, 2147483647].all fun day =>
  (print (Int32.ofInt day)).isNone
#guard ["", "0000-02-30", "1900-02-29", "1970-1-01", "1970/01/01", "1970-01-01x",
  "1970-00-01", "1970-01-00", "1970-01-01 ", "１９７０-01-01", "10000-01-01", "-0001-12-31"].all
    fun text => (parse (bytes text)).isNone

#guard rejectsWire (bytes "日付\r\nN\r\n") false (.requiredNull 0 0)
#guard rejectsWire (bytes "日付\r\nT\r\n") true (.csv (.parseCell 0))
#guard rejectsWire (bytes "日付\r\n\r\n") true (.csv (.invalidTag 0))
#guard rejectsWire (bytes "日付\r\nN,\r\n") true (.csv (.width 1 2))
#guard rejectsWire (bytes "other\r\nN\r\n") true (.csv .headerMismatch)
#guard rejectsWire (bytes "日付\r\n\"T1970-01-01\r\n") true (.csv .malformedWire)
#guard rejectsWire (bytes "日付\r\n" ++ [0x54, 0xC0, 0xAF, 0x0D, 0x0A]) true (.csv .malformedWire)
#guard match encode (schema false) nullable [fun _ => some (Int32.ofInt 0), fun _ => none] with
  | .error (.requiredNull 1 0) => true
  | _ => false
#guard match encode (schema true) nullable [fun _ => some (Int32.ofInt (-719529))] with
  | .error (.csv (.printCell 0)) => true
  | _ => false
