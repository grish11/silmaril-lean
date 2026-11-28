module

public import Silmaril.Formats.ThriftCompact.Traversal.Defs

public section

namespace Silmaril.Formats.ThriftCompact.Traversal

/-- Preserve the next offset while translating a callback's value and error. -/
@[expose] def mapReadResult {α β ε δ : Type} (value : α → β) (error : ε → δ)
    (result : Except ε (α × Nat)) : Except δ (β × Nat) :=
  (result.map fun (item, next) => (value item, next)).mapError error

/-- Exact callback extents in the original collection order. -/
inductive ListTrace {α ε : Type} (read : Nat → Except ε (α × Nat)) :
    Nat → List α → Nat → Prop where
  | nil (offset : Nat) : ListTrace read offset [] offset
  | cons {start next stop : Nat} {item : α} {rest : List α}
      (head : read start = .ok (item, next)) (tail : ListTrace read next rest stop) :
      ListTrace read start (item :: rest) stop

end Silmaril.Formats.ThriftCompact.Traversal
