module

public import Silmaril.Formats.Dasl.Encode.Thms
public import Silmaril.Formats.Dasl.StringDiagram.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.StringDiagram.Wire

open Encode

variable {Name : Type}

def boxFields : TotalCodec (Box (Shallow Name)) (List (Shallow Name)) where
  encode box := [signed.encode box.inputs, signed.encode box.outputs, box.label]
  decode?
    | [inputs, outputs, label] => do
      pure ⟨← signed.decode? inputs, ← signed.decode? outputs, label⟩
    | _ => none
  recovers := by
    intro ⟨inputs, outputs, label⟩
    simp [signed.recovers]

def box : TotalCodec (Box (Shallow Name)) (Shallow Name) := boxFields.then list

def parts : TotalCodec (Diagram (Shallow Name)) (List (Shallow Name)) where
  encode d := [signed.encode d.inputs, signed.encode d.exports, (listOf box).encode d.boxes,
    (listOf signed).encode d.boxSources, (listOf signed).encode d.exportSources]
  decode?
    | [inputs, exports, boxes, boxSources, exportSources] => do
      pure ⟨← signed.decode? inputs, ← signed.decode? exports, ← (listOf box).decode? boxes,
        ← (listOf signed).decode? boxSources, ← (listOf signed).decode? exportSources⟩
    | _ => none
  recovers := by
    intro ⟨inputs, exports, boxes, boxSources, exportSources⟩
    simp [signed.recovers, TotalCodec.recovers]

/-- The reserved root tag is checked before parsing the body. -/
def tag : String := "string-diagram/v1"

def envelope : TotalCodec (Shallow Name) (List (Shallow Name)) where
  encode body := [.string tag, body]
  decode?
    | [.string version, body] => if version = tag then some body else none
    | _ => none
  recovers _ := by simp

/-- The raw schema recognizes exact constructor shapes. Its signed fields can
still be invalid counts or references. -/
def raw : TotalCodec (Diagram (Shallow Name)) (Shallow Name) :=
  ((parts.then list).then envelope).then list

/-- The checked codec validates structure after parsing. Links in labels stay shallow. -/
def checked : TotalCodec (Checked (Shallow Name)) (Shallow Name) :=
  (⟨Subtype.val, check?, fun ⟨_, valid⟩ => by simp [check?, valid]⟩ :
    TotalCodec (Checked (Shallow Name)) (Diagram (Shallow Name))).then raw

end Silmaril.Formats.Dasl.StringDiagram.Wire
