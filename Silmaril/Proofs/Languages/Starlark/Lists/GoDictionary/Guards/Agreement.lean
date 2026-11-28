module

public import Silmaril.Languages.Starlark.Lists.GoDictionary.Guards.Defs
import Silmaril.Languages.Starlark.Lists.GoDictionary.Abstraction.Thms
public import Silmaril.Languages.Starlark.Lists.Iteration.Defs
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Guards.Physical

public section

namespace Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Guards

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Lists (State Entry writeDict putEntry)
open Silmaril.Languages.Starlark.Lists.GoDictionary (hashKey)
open Silmaril.Languages.Starlark.Lists.GoDictionary.Guards

theorem allowed_iff (table : Table) :
    table.rejection = none ↔ table.frozen = false ∧ table.activeIterators = 0 := by
  cases frozen : table.frozen <;> simp [Table.rejection, frozen]

private theorem init_related (state : State) (address : Lists.Address) (table : Table)
    (entries : List Entry) (related : Related state address table entries) :
    Related state address table.initialize entries := by
  exact ⟨related.cell, related.active, related.rows⟩

theorem zero_related (state : State) (address : Lists.Address) (table : Table)
    (cell : state.heap[address]? = some ⟨.dict [], table.frozen⟩)
    (active : table.frozen = false → (0 < table.activeIterators ↔ address ∈ state.iterators)) (zero : table.contents = none) :
    Related state address table [] := by
  refine ⟨cell, active, ?_⟩
  simpa [Table.rows, zero] using
    Lists.GoDictionary.Abstraction.empty_related state.heap Lists.GoDictionary.Abstraction.scalarProfile

theorem enterIterator_related (state : State) (address : Lists.Address) (table : Table)
    (entries : List Entry) (related : Related state address table entries) :
    Related (Lists.Iteration.pushIterator state address) address table.enterIterator entries := by
  cases frozen : table.frozen
  · refine ⟨?_, ?_, ?_⟩
    · simpa [Table.enterIterator, Lists.Iteration.pushIterator, frozen] using related.cell
    · simp [Table.enterIterator, Lists.Iteration.pushIterator, frozen]
    · simpa [Table.enterIterator, Lists.Iteration.pushIterator, frozen, Table.rows] using related.rows
  · refine ⟨?_, ?_, ?_⟩
    · simpa [Table.enterIterator, Lists.Iteration.pushIterator, frozen] using related.cell
    · simp [Table.enterIterator, frozen]
    · simpa [Table.enterIterator, Lists.Iteration.pushIterator, frozen] using related.rows

theorem guard_agrees (state : State) (address : Lists.Address) (table : Table) (entries : List Entry)
    (key value : Lists.Value) (reason : Rejection)
    (related : Related state address table entries) (blocked : table.rejection = some reason) :
    Lists.GoDictionary.Guards.set state.heap table key value = .error (.guard reason) table ∧
      delete state.heap table key = .error (.guard reason) table ∧
      writeDict address key value state = .error (reason.canonicalError address) state := by
  obtain ⟨setBlocked, deleteBlocked⟩ := rejects state.heap table key value reason blocked
  refine ⟨setBlocked, deleteBlocked, ?_⟩
  cases frozen : table.frozen with
  | true =>
    simp [Table.rejection, frozen] at blocked
    subst reason
    simp [writeDict, Lists.editCell, Lists.getCell, bind, EStateM.bind, related.cell, frozen,
      Rejection.canonicalError]
  | false =>
    by_cases active : 0 < table.activeIterators
    · simp [Table.rejection, frozen, active] at blocked
      subst reason
      have iterating := (related.active frozen).mp active
      simp [writeDict, Lists.editCell, Lists.getCell, bind, EStateM.bind, related.cell, frozen, iterating,
        Rejection.canonicalError]
    · simp [Table.rejection, frozen, active] at blocked

theorem writeDict_dangling (state : State) (address : Lists.Address) (key value : Lists.Value)
    (missing : state.heap[address]? = none) :
    writeDict address key value state = .error (.danglingAddress address) state := by
  simp [writeDict, Lists.editCell, Lists.getCell, bind, EStateM.bind, missing]

theorem writeDict_unhashable (state : State) (address : Lists.Address) (table : Table)
    (entries : List Entry) (key value : Lists.Value)
    (related : Related state address table entries) (allowed : table.rejection = none)
    (shape : Unhashable key) :
    Lists.GoDictionary.Guards.set state.heap table key value =
        .error (.table (.unsupportedKey key)) table.initialize ∧
      writeDict address key value state = .error (.unhashableKey key) state := by
  obtain ⟨mutable, inactive⟩ := (allowed_iff table).mp allowed
  have noIterator : address ∉ state.iterators := by
    intro active
    have positive := (related.active mutable).mpr active
    omega
  have hashed : hashKey state.heap key = .error (.unsupportedKey key) := by
    cases shape <;> rfl
  have encoded : state.keyOf key = .error (.unhashableKey key) := by
    cases shape <;> rfl
  exact ⟨set_hash_error state.heap table key value _ allowed hashed, by
    simp [writeDict, Lists.editCell, Lists.getCell, related.cell, mutable, noIterator, encoded, bind,
      EStateM.bind, Except.bind]⟩

theorem writeDict_lockstep (state : State) (address : Lists.Address) (table : Table)
    (entries : List Entry) (key value : Lists.Value) (related : Related state address table entries)
    (domain : (∃ scalar, key = .scalar scalar) ∨ Unhashable key) :
    AssignsTogether state address table entries
      (Lists.GoDictionary.Guards.set state.heap table key value)
      (writeDict address key value state) := by
  cases guard : table.rejection with
  | some reason =>
    obtain ⟨physical, _, canonical⟩ :=
      guard_agrees state address table entries key value reason related guard
    rw [physical, canonical]
    exact .rejected reason related
  | none =>
    rcases domain with ⟨scalar, rfl⟩ | shape
    · obtain ⟨mutable, noActive⟩ := (allowed_iff table).mp guard
      have inactive : address ∉ state.iterators := by
        intro present
        have positive := (related.active mutable).mpr present
        omega
      have cell : state.heap[address]? = some ⟨.dict entries, false⟩ := by
        simpa only [mutable] using related.cell
      let query : Lists.GoDictionary.Abstraction.KeyObservation :=
        ⟨[.scalar (Lists.ScalarKey.ofValue scalar)],
          Lists.GoDictionary.storedHash (Lists.GoDictionary.scalarHash scalar)⟩
      have admitted : Lists.GoDictionary.Abstraction.scalarProfile (.scalar scalar) = some query := rfl
      obtain ⟨next, physical, canonical, keep⟩ := Lists.GoDictionary.Abstraction.writeDict_agrees
        state address _ table.rows entries (.scalar scalar) value query
        (Lists.GoDictionary.Abstraction.scalar_coherent state.heap) related.rows admitted cell inactive
      rw [set_ready state.heap table _ value next guard physical, canonical]
      apply AssignsTogether.assigned
      exact ⟨by simpa only [mutable] using
        Array.getElem?_setIfInBounds_self_of_lt (Array.getElem?_eq_some_iff.mp cell).choose,
        related.active, keep (Lists.GoDictionary.Abstraction.scalar_coherent _)⟩
    · obtain ⟨physical, canonical⟩ :=
        writeDict_unhashable state address table entries key value related guard shape
      rw [physical, canonical]
      exact .unhashable key shape (init_related state address table entries related)

end Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Guards
