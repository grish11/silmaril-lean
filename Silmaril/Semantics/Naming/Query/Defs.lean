module

public import Silmaril.Semantics.Naming.Defs

@[expose] public section

namespace Silmaril.Semantics.Naming

inductive ReadFailure where
  | missing
  | invalid
  deriving DecidableEq

/-- Queries may return incomplete views. A successful read must belong to the
reference relation. A failure makes no assertion about absence in that relation. -/
structure Queries {Name Obj Blob : Type} (reference : Stores Name Obj Blob) where
  readObject : (name : Name) → Except ReadFailure {payload // reference.objects name payload}
  readBlob : (name : Name) → Except ReadFailure {payload // reference.blobs name payload}

end Silmaril.Semantics.Naming
