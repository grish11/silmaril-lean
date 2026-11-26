module

public import Silmaril.Formats.ThriftCompact.Traversal.List.Defs
import all Silmaril.Formats.ThriftCompact.Traversal.Defs

namespace Silmaril.Proofs.Formats.ThriftCompact.Traversal

open Silmaril.Formats.ThriftCompact
open Silmaril.Formats.ThriftCompact.Traversal

private theorem mapGo {α β ε δ : Type} (value : α → β) (error : ε → δ)
    (read : Nat → Except ε (α × Nat)) (size start : Nat) (acc : List α) :
    readList.go (fun offset => mapReadResult value error (read offset)) size (acc.map value) start =
      mapReadResult (List.map value) error (readList.go read size acc start) := by
  induction size generalizing start acc with
  | zero => simp [readList.go, mapReadResult, Except.map, Except.mapError, List.map_reverse]
  | succ size ih =>
    cases item : read start with
    | error reason => simp [readList.go, item, mapReadResult, Except.map, Except.mapError, bind, Except.bind]
    | ok pair =>
      obtain ⟨itemValue, next⟩ := pair
      simpa [readList.go, item, mapReadResult, Except.map, Except.mapError, bind, Except.bind] using
        ih next (itemValue :: acc)

public theorem readList_map {α β ε δ : Type} (reader : Reader) (fail : Traversal.Error → ε)
    (type : ValueType) (read : Nat → Except ε (α × Nat)) (value : α → β) (error : ε → δ)
    (start : Nat) :
    readList reader (error ∘ fail) type (fun offset => mapReadResult value error (read offset)) start =
      mapReadResult (List.map value) error (readList reader fail type read start) := by
  cases collection : readCollectionHeader reader.mode reader.limits.maxCollectionSize reader.source start with
  | error reason => simp [readList, compact, collection, mapReadResult, Except.map, Except.mapError, bind, Except.bind]
  | ok pair =>
    obtain ⟨header, first⟩ := pair
    by_cases kind : header.elementType = type
    · simpa [readList, compact, collection, kind, Except.mapError, bind, Except.bind] using
        mapGo value error read header.size first []
    · simp [readList, compact, collection, kind, mapReadResult, Except.map, Except.mapError,
        bind, Except.bind, throwThe, throw]
      rfl

private theorem traceGo {α ε : Type} (read : Nat → Except ε (α × Nat))
    {size start next : Nat} {acc items : List α}
    (parsed : readList.go read size acc start = .ok (items, next)) :
    ∃ suffix, items = acc.reverse ++ suffix ∧ suffix.length = size ∧ ListTrace read start suffix next := by
  induction size generalizing start next acc items with
  | zero =>
    obtain ⟨rfl, rfl⟩ := Except.ok.inj parsed
    exact ⟨[], by simp, rfl, .nil _⟩
  | succ size ih =>
    cases item : read start with
    | error reason => simp [readList.go, item, bind, Except.bind] at parsed
    | ok pair =>
      obtain ⟨found, stop⟩ := pair
      simp only [readList.go, item, bind, Except.bind] at parsed
      obtain ⟨suffix, itemsEq, length, trace⟩ := ih parsed
      exact ⟨found :: suffix, by simpa [List.reverse_cons, List.append_assoc] using itemsEq,
        congrArg Nat.succ length, .cons item trace⟩

public theorem readList_trace {α ε : Type} {reader : Reader} {fail : Traversal.Error → ε}
    {type : ValueType} {read : Nat → Except ε (α × Nat)} {start next : Nat} {items : List α}
    (parsed : readList reader fail type read start = .ok (items, next)) :
    ∃ header first, readCollectionHeader reader.mode reader.limits.maxCollectionSize reader.source start =
        .ok (header, first) ∧ header.elementType = type ∧ header.size = items.length ∧
      ListTrace read first items next := by
  cases collection : readCollectionHeader reader.mode reader.limits.maxCollectionSize reader.source start with
  | error reason => simp [readList, compact, collection, Except.mapError, bind, Except.bind] at parsed
  | ok pair =>
    obtain ⟨header, first⟩ := pair
    by_cases kind : header.elementType = type
    · simp [readList, compact, collection, kind, Except.mapError, bind, Except.bind] at parsed
      obtain ⟨suffix, itemsEq, length, trace⟩ := traceGo read parsed
      simp only [List.reverse_nil, List.nil_append] at itemsEq
      subst items
      exact ⟨header, first, rfl, kind, length.symm, trace⟩
    · simp [readList, compact, collection, kind, Except.mapError, bind, Except.bind, throwThe, throw] at parsed

public theorem ListTrace.mem_read {α ε : Type} {read : Nat → Except ε (α × Nat)}
    {start next : Nat} {items : List α} (trace : ListTrace read start items next)
    {item : α} (member : item ∈ items) : ∃ a b, read a = .ok (item, b) := by
  induction trace with
  | nil => simp at member
  | cons head _ ih =>
    rcases List.mem_cons.mp member with same | later
    · exact ⟨_, _, same ▸ head⟩
    · exact ih later

end Silmaril.Proofs.Formats.ThriftCompact.Traversal
