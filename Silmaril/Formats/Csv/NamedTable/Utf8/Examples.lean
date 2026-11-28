module

import Silmaril.Formats.Csv.NamedTable.Utf8.Thms
meta import Silmaril.Formats.Csv.NamedTable.Utf8.Defs

/-! Executable named UTF-8 import, export, and rejection examples. -/

namespace Silmaril.Formats.Csv.NamedTable.Utf8

open Silmaril.Relational
open Silmaril.Formats.Relational.NamedTable (Packed)

private meta def Value (_ : Bool) := String

private meta def codecs (k : Bool) : Typed.CellCodec (Value k) := Typed.Utf8.string

private meta def bytes (text : String) : Bytes := text.toUTF8.data.toList

private meta def schema : Typed.Schema Bool := ⟨1, fun _ => (bytes "都市", false)⟩

private meta def wrongKind : Typed.Schema Bool := ⟨1, fun _ => (bytes "都市", true)⟩

private meta def values : List (Option String) :=
  [none, some "", some "N", some "T", some "東京,🙂\"\r\n"]

private meta def source : Packed Nat Field Value := fun name =>
  if name = 0 then some ⟨schema, values.map (fun value _ => value)⟩ else none

private meta def target : Packed Nat Field Value := fun name =>
  if name = 0 then some ⟨schema, [fun _ => some "保持"]⟩ else none

private meta def observe (db : Packed Nat Field Value) (name : Nat) :
    Option (List (List (Option String))) :=
  (Scan.observePacked db name).map fun table => table.rows.map List.ofFn

private meta def input : Bytes := bytes "都市\r\nN\r\nT\r\nTN\r\nTT\r\n\"T東京,🙂\"\"\r\n\""

private meta def canonical : Bytes :=
  bytes "\"都市\"\r\n\"N\"\r\n\"T\"\r\n\"TN\"\r\n\"TT\"\r\n\"T東京,🙂\"\"\r\n\"\r\n"

#guard (importCsv target 1 schema schema codecs input).map (observe · 1) =
  .ok (some (values.map fun value => [value]))
#guard (importCsv target 1 schema schema codecs input).map (observe · 0) = .ok (some [[some "保持"]])
#guard (exportCsv source 0 codecs).map Prod.snd = .ok canonical
#guard (exportCsv source 0 codecs).toOption.map (fun exported => List.ofFn exported.1.kind) =
  some [(bytes "都市", false)]
#guard (exportCsv source 0 codecs).toOption.bind (fun (declared, wire) =>
    (importCsv target 1 schema declared codecs wire).toOption.map (observe · 1)) =
  some (some (values.map fun value => [value]))

#guard (importCsv target 0 schema schema codecs input).map (fun _ => ()) = .error .nameConflict
#guard (importCsv target 0 schema schema codecs [0x80]).map (fun _ => ()) = .error .nameConflict
#guard (importCsv target 1 wrongKind schema codecs input).map (fun _ => ()) = .error .schemaMismatch
#guard (importCsv target 1 schema schema codecs (bytes "空港\r\nN")).map (fun _ => ()) =
  .error (.openError .headerMismatch)
#guard (importCsv target 1 schema schema codecs (bytes "都市\r\nN,N")).map (fun _ => ()) =
  .error (.openError (.width 1 2))
#guard (importCsv target 1 schema schema codecs (bytes "都市\r\nN\r\nN東京")).map (fun _ => ()) =
  .error (.openError (.invalidTag 0))

-- The valid first row cannot be inserted when a later field is malformed.
#guard (importCsv target 1 schema schema codecs (bytes "都市\r\nT先\r\nT" ++ [0xF0, 0x9F])).map
  (fun _ => ()) = .error (.openError .malformedWire)
#guard (exportCsv target 1 codecs).map Prod.snd = .error .missingName

private meta def controlSource : Packed Nat Field Value := fun _ =>
  some ⟨schema, [fun _ => some "東京\t"]⟩

#guard (exportCsv controlSource 0 codecs).map Prod.snd = .error (.encodeError .unrepresentableWire)
#guard (NamedTable.exportCsv source 0 codecs).map Prod.snd = .error (.encodeError .unrepresentableWire)

private meta def zero : Typed.Schema Bool := ⟨0, fun i => i.elim0⟩

private meta def zeroSource : Packed Nat Field Value := fun _ =>
  some ⟨zero, [fun i => i.elim0, fun i => i.elim0]⟩

private meta def zeroWire : Bytes := bytes "\"\"\r\n\"\"\r\n\"\"\r\n"

#guard (exportCsv zeroSource 0 codecs).map Prod.snd = .ok zeroWire
#guard (importCsv target 1 zero zero codecs zeroWire).map (fun loaded =>
  (Scan.observePacked loaded 1).map Scan.Observation.rowCount) = .ok (some 2)
#guard (importCsv target 1 zero zero codecs (bytes "\"\"\r\nN")).map (fun _ => ()) =
  .error (.openError .zeroColumnMarker)

end Silmaril.Formats.Csv.NamedTable.Utf8
