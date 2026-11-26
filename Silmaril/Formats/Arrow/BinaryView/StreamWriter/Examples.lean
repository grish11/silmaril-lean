module

public import Silmaril.Formats.Arrow.BinaryView.StreamWriter.Defs
meta import Silmaril.Formats.Arrow.BinaryView.StreamWriter.Defs

@[expose] public section

namespace Silmaril.Formats.Arrow.BinaryView.StreamWriter.Examples

def binaryCases : List (String × String × Bool × List (List (Option KBytes))) :=
  [("nullable", "blob", true,
      [[none, some .empty, some (.leaf 12 255), some (.leaf 13 1)], [], [some (.leaf 1 2)]]),
    ("required", "bytes雪", false, [[some (.leaf 13 3), some .empty]]),
    ("one-empty", "empty", false, [[]]),
    ("schema-only", "empty", false, [])]

def utf8Field : Schema.Field := ⟨"text", true, .utf8⟩

def utf8Batches : List (List (Option String)) :=
  [[some "", some "éééééé", some "ééééééx", none], []]

private def emits (field : Schema.Field) (batches : List (Schema.Values field.kind)) : Bool :=
  match emit {} {} field batches with
  | .error _ => false
  | .ok wire =>
    match Stream.read {} {} wire with
    | .error _ => false
    | .ok decoded => decide (Agrees field batches decoded)

#guard binaryCases.all fun (_, name, nullable, batches) => emits ⟨name, nullable, .binary⟩ batches

#guard emits utf8Field utf8Batches

private def rejects (result : Except Error KBytes) (expected : Error) : Bool :=
  match result with
  | .error actual => decide (actual = expected)
  | .ok _ => false

#guard rejects (emit {} {} ⟨"required", false, .binary⟩ [[some .empty], [none]])
  (.record 1 (.column .nullInRequired))
#guard rejects (emit { batches := 0 } {} ⟨"empty", false, .binary⟩ [[]]) (.ipc (.limit .batches))
#guard match emit { batches := 0 } {} ⟨"empty", false, .binary⟩ [] with
  | .ok _ => true
  | .error _ => false
#guard rejects (emit { fields := 0 } {} ⟨"empty", false, .binary⟩ []) (.ipc (.limit .fields))
#guard rejects (emit { rows := 0 } {} ⟨"blob", true, .binary⟩ [[], [none]])
  (.record 1 (.ipc (.limit .rows)))
#guard rejects (emit { metadataBytes := 176 } {} ⟨"blob", true, .binary⟩ [[some (.leaf 13 1)]])
  (.record 0 (.ipc (.limit .metadataBytes)))
#guard rejects (emit { bodyBytes := 16 } {} ⟨"blob", true, .binary⟩ [[some .empty]])
  (.record 0 (.ipc (.limit .bodyBytes)))
#guard rejects (emit {} { dataBuffers := 0 } ⟨"blob", true, .binary⟩ [[some (.leaf 13 1)]])
  (.record 0 (.column .dataBufferLimit))
#guard match emit {} { dataBuffers := 0 } ⟨"blob", true, .binary⟩ [[some (.leaf 12 1)], []] with
  | .ok _ => true
  | .error _ => false

end Silmaril.Formats.Arrow.BinaryView.StreamWriter.Examples
