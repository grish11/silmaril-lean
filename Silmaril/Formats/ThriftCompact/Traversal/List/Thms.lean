module

public import Silmaril.Formats.ThriftCompact.Traversal.List.Defs
import Silmaril.Proofs.Formats.ThriftCompact.Traversal.List

public section

namespace Silmaril.Formats.ThriftCompact.Traversal

theorem readList_map {α β ε δ : Type} (reader : Reader) (fail : Traversal.Error → ε)
    (type : ValueType) (read : Nat → Except ε (α × Nat)) (value : α → β) (error : ε → δ)
    (start : Nat) :
    readList reader (error ∘ fail) type (fun offset => mapReadResult value error (read offset)) start =
      mapReadResult (List.map value) error (readList reader fail type read start) :=
  Proofs.Formats.ThriftCompact.Traversal.readList_map reader fail type read value error start

theorem readList_trace {α ε : Type} {reader : Reader} {fail : Traversal.Error → ε}
    {type : ValueType} {read : Nat → Except ε (α × Nat)} {start next : Nat} {items : List α}
    (parsed : readList reader fail type read start = .ok (items, next)) :
    ∃ header first, readCollectionHeader reader.mode reader.limits.maxCollectionSize reader.source start =
        .ok (header, first) ∧ header.elementType = type ∧ header.size = items.length ∧
      ListTrace read first items next :=
  Proofs.Formats.ThriftCompact.Traversal.readList_trace parsed

theorem ListTrace.mem_read {α ε : Type} {read : Nat → Except ε (α × Nat)}
    {start next : Nat} {items : List α} (trace : ListTrace read start items next)
    {item : α} (member : item ∈ items) : ∃ a b, read a = .ok (item, b) :=
  Proofs.Formats.ThriftCompact.Traversal.ListTrace.mem_read trace member

end Silmaril.Formats.ThriftCompact.Traversal
