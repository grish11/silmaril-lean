module

public import Silmaril.Formats.Arrow.MixedFlat.StreamWriter.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.StreamWriter.Defs

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.StreamWriter.Examples

def nullable : Schema := ⟨.intFirst, "signed雪", true, "blob", true⟩

def required : Schema := ⟨.viewFirst, "signed雪", false, "blob", false⟩

def first : BatchInput :=
  ⟨4, [some 1, none, some (-7), some (-2147483648)],
    [none, some .empty, some (.leaf 12 255), some (.leaf 4 0x04030201 ++ .leaf 9 0)]⟩

def empty : BatchInput := ⟨0, [], []⟩

def last : BatchInput :=
  ⟨2, [some 2147483647, some 0], [some (.leaf 12 255), some (.leaf 1 2)]⟩

def cases : List (String × Schema × List BatchInput) :=
  [("int-first", nullable, [first, empty, last]),
    ("view-first", { nullable with order := .viewFirst }, [first, empty, last]),
    ("required", required, [last]),
    ("schema-only", { required with viewNullable := true }, []),
    ("one-empty", { required with viewNullable := true }, [empty])]

private def checks (schema : Schema) (batches : List BatchInput) : Bool :=
  match emit {} schema batches with
  | .error _ => false
  | .ok wire =>
    match Stream.read {} wire with
    | .error _ => false
    | .ok observed =>
      decide (observed.fields = schema.fields ∧
        observed.batches.map observeBatch = batches.map (BatchInput.observe schema))

#guard cases.all fun (_, schema, batches) => checks schema batches

private def rejects (result : Except Error KBytes) (expected : Error) : Bool :=
  match result with
  | .error cause => decide (cause = expected)
  | .ok _ => false

#guard rejects (emit { observation := { ipc := { batches := 0 } } } required [empty])
  (.ipc (.limit .batches))
#guard (emit { observation := { ipc := { batches := 0 } } } required []).isOk
#guard rejects (emit { observation := { ipc := { fields := 1 } } } required [])
  (.schema (.limit .fields))
#guard rejects (emit { observation := { ipc := { metadataBytes := 1 } } } required [])
  (.schema (.limit .metadataBytes))
#guard rejects (emit { observation := { totalRows := 4 } } nullable [first, empty, last])
  (.budget 2 (.limit .totalRows))
#guard rejects (emit { observation := { totalCells := 11 } } nullable [first, empty, last])
  (.budget 2 (.limit .totalCells))
#guard rejects (emit { observation := { ipc := { rows := 3 } } } nullable [empty, first])
  (.batch 1 (.ipc (.limit .rows)))
#guard rejects (emit { observation := { ipc := { bodyBytes := 111 } } } nullable [empty, first])
  (.batch 1 (.ipc (.limit .bodyBytes)))
#guard (emit { observation := { ipc := { bodyBytes := 112 } } } nullable [first, first]).isOk
#guard rejects (emit { totalDataBuffers := 0 } nullable [empty, first])
  (.batch 1 (.metadata .totalDataBufferLimit))
#guard rejects (emit {} nullable [first, { last with viewValues := [] }])
  (.batch 1 (.rowCount 1 2 0))
#guard rejects (emit {} required [last, first])
  (.batch 1 (.nullInRequired 1))
#guard rejects (emit {} required [last, { last with viewValues := [none, some .empty] }])
  (.batch 1 (.view 0 .nullInRequired))

end Silmaril.Formats.Arrow.MixedFlat.StreamWriter.Examples
