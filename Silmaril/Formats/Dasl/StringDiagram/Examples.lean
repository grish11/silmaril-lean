module

import Silmaril.Formats.Dasl.StringDiagram.Thms
import Silmaril.Formats.Dasl.StringDiagram.Wire.Defs

namespace Silmaril.Formats.Dasl.StringDiagram

private def arr : List (Shallow String) → Shallow String := Encode.list.encode
private def int (i : Int64) : Shallow String := .i64 i.toUInt64

private def diagram : Diagram (Shallow String) :=
  ⟨2, 2, [⟨1, 2, .string "f"⟩, ⟨2, 1, .dict {"op"} (fun _ => .string "g")⟩, ⟨0, 0, .null⟩],
    [0, 3, 1], [2, 4]⟩

private def tree : Shallow String :=
  arr [.string "string-diagram/v1", arr [int 2, int 2,
    arr [arr [int 1, int 2, .string "f"],
      arr [int 2, int 1, .dict {"op"} (fun _ => .string "g")], arr [int 0, int 0, .null]],
    arr [int 0, int 3, int 1], arr [int 2, int 4]]]

example : diagram.wellFormed = true := by decide
example : splitInputs? diagram.inputWidths diagram.boxSources = some [[0], [3, 1], []] := by decide
example : Wire.raw.encode diagram = tree := rfl
example : Wire.checked.decode? tree = some ⟨diagram, by decide⟩ :=
  Wire.checked.recovers ⟨diagram, by decide⟩

/-- Repeated uses, a dangling output and an opaque raw link all survive. -/
private def sharing : Diagram (Shallow String) :=
  ⟨1, 2, [⟨0, 1, .ref (.blob "blob")⟩], [], [0, 0]⟩

example : sharing.wellFormed = true := by decide
example : Wire.checked.decode? (Wire.raw.encode sharing) = some ⟨sharing, by decide⟩ :=
  Wire.checked.recovers ⟨sharing, by decide⟩

private def cycle : Diagram (Shallow String) := ⟨0, 0, [⟨1, 1, .null⟩], [0], []⟩

example : cycle.wellFormed = true := by decide
example : ({ diagram with boxSources := [0, 5, 1] }).wellFormed = false := by decide
example : ({ diagram with exportSources := [2] }).wellFormed = false := by decide
example : ({ diagram with inputs := -1 }).wellFormed = false := by decide
example : ({ sharing with inputs := 9223372036854775807 }).wellFormed = false := by decide

example : (Wire.checked.decode? (Wire.raw.encode { diagram with exportSources := [] })).isNone := by
  decide

example : (Wire.raw.decode? (arr [.string "string-diagram/v2", .null])).isNone := by decide
example : (Wire.raw.decode? (arr [.string Wire.tag, arr [int 0, int 0, arr [], arr []]])).isNone := by
  decide

end Silmaril.Formats.Dasl.StringDiagram
