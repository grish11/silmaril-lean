module

public import Silmaril.Formats.Arrow.MixedFlat.Writer.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.Writer.Defs

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.Writer.Examples

def mixed : Input :=
  ⟨.intFirst, 4, "signed", true, [some 1, none, some (-7), some (-2147483648)],
    "octets", true, [none, some .empty, some (.leaf 12 255), some (.leaf 4 0x04030201 ++ .leaf 9 0)]⟩

def inline : Input :=
  ⟨.viewFirst, 2, "signed", false, [some 2147483647, some 0],
    "octets", false, [some (.leaf 12 255), some .empty]⟩

def empty : Input :=
  ⟨.intFirst, 0, "signed", false, [], "octets", true, []⟩

def cases : List (String × Input) :=
  [("int-first", mixed), ("view-first", { mixed with order := .viewFirst }),
    ("inline", inline), ("empty", empty)]

private def check (input : Input) (count : Nat) (expected : List Buffer) : Bool :=
  match emit {} input with
  | .error _ => false
  | .ok output =>
    decide (output.metadata.counts = [count] ∧ output.metadata.batch.buffers = expected) &&
      match MixedFlat.readParsed {} input.fields output.metadata output.body with
      | .error _ => false
      | .ok values => decide (values.rowCount = input.rowCount ∧
          observeColumns values.columns = some input.observe)

#guard check mixed 1 [⟨0, 1⟩, ⟨8, 16⟩, ⟨24, 1⟩, ⟨32, 64⟩, ⟨96, 13⟩]
#guard check { mixed with order := .viewFirst } 1
  [⟨0, 1⟩, ⟨8, 64⟩, ⟨72, 13⟩, ⟨88, 1⟩, ⟨96, 16⟩]
#guard check inline 0 [⟨0, 1⟩, ⟨8, 32⟩, ⟨40, 1⟩, ⟨48, 8⟩]
#guard check empty 0 [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]

private def rejects (input : Input) (expected : Error) (limits : MixedFlat.Limits := {}) : Bool :=
  match emit limits input with
  | .error cause => decide (cause = expected)
  | .ok _ => false

#guard rejects { mixed with order := .viewFirst, intValues := [none] } (.rowCount 1 4 1)
#guard rejects { mixed with viewValues := [] } (.rowCount 1 4 0)
#guard rejects { mixed with intNullable := false } (.nullInRequired 0)
#guard rejects { mixed with viewNullable := false } (.view 1 .nullInRequired)
#guard rejects mixed (.metadata .totalDataBufferLimit) { totalDataBuffers := 0 }
#guard rejects mixed (.view 1 .dataBufferLimit) { view := { dataBuffers := 0 } }
#guard rejects mixed (.ipc (.limit .bodyBytes)) { observation := { ipc := { bodyBytes := 111 } } }
#guard rejects mixed (.ipc (.limit .metadataBytes)) { observation := { ipc := { metadataBytes := 239 } } }

end Silmaril.Formats.Arrow.MixedFlat.Writer.Examples
