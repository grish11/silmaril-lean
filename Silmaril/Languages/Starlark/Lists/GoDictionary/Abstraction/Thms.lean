module

public import Silmaril.Languages.Starlark.Lists.GoDictionary.Abstraction.Defs
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Abstraction.Scalars
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Abstraction.Lookup
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Abstraction.Assignment
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Abstraction.Denotation

public section

namespace Silmaril.Languages.Starlark.Lists.GoDictionary.Abstraction

open Deletion (Table)

/-- All scalar keys satisfy the profile laws in any heap. -/
theorem scalar_coherent (heap : Heap) : Coherent heap scalarProfile :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Abstraction.scalar_coherent heap

/-- The canonical live entries are the ordered physical rows with their checked codes. -/
theorem related_rows (heap : Heap) (profile : KeyProfile) (table : Table) (entries : List Entry)
    (related : Related heap profile table entries) :
    table.entries.map (observeRow profile) = entries.map some :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Abstraction.related_rows heap profile table entries related

/-- Observation retains original key identities, original values, and iteration order. -/
theorem ordered_key_values (heap : Heap) (profile : KeyProfile) (table : Table) (entries : List Entry)
    (related : Related heap profile table entries) :
    table.entries.map (fun row => (row.key, row.value)) =
      entries.map (fun entry => (entry.key, entry.value)) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Abstraction.ordered_key_values heap profile table entries related

/-- Both lookups select the same full entry or the same miss. -/
theorem lookup_agrees (heap : Heap) (profile : KeyProfile) (table : Table) (entries : List Entry)
    (key : Value) (query : KeyObservation) (laws : Coherent heap profile)
    (related : Related heap profile table entries) (admitted : profile key = some query) :
    lookupEntry heap profile table key = .ok (findEntry query.code entries) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Abstraction.lookup_agrees heap profile table entries key query laws related admitted

/-- The initialized empty physical table represents the empty canonical dictionary. -/
theorem empty_related (heap : Heap) (profile : KeyProfile) :
    Related heap profile Table.empty [] :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Abstraction.empty_related heap profile

/-- Physical assignment preserves the relation to canonical putEntry on inserts and replacements. -/
theorem set_agrees (heap : Heap) (profile : KeyProfile) (table : Table) (entries : List Entry)
    (key value : Value) (query : KeyObservation) (laws : Coherent heap profile)
    (related : Related heap profile table entries) (admitted : profile key = some query) :
    ∃ next, Deletion.set heap table key value = .ok next ∧
      Related heap profile next (putEntry ⟨key, query.code, value⟩ entries) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Abstraction.set_agrees heap profile table entries key value query laws related admitted

/-- The relation transfers between heaps with the same coherent key observations. -/
theorem related_heap (heap after : Heap) (profile : KeyProfile) (table : Table) (entries : List Entry)
    (beforeLaws : Coherent heap profile) (afterLaws : Coherent after profile)
    (related : Related heap profile table entries) : Related after profile table entries :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Abstraction.related_heap heap after profile table entries beforeLaws afterLaws related

/-- The physical observation matches live canonical lookup and the subscript read result. -/
theorem readDict_agrees (state : State) (address : Lists.Address) (profile : KeyProfile)
    (table : Table) (entries : List Entry) (key : Value) (query : KeyObservation)
    (laws : Coherent state.heap profile) (related : Related state.heap profile table entries)
    (admitted : profile key = some query) (frozen : Bool)
    (cell : state.heap[address]? = some ⟨.dict entries, frozen⟩) :
    ∃ found, lookupEntry state.heap profile table key = .ok found ∧
      Lists.Comparison.lookupDictionary state.heap address key = .ok found ∧
      readDict address key state = (match found with
        | some entry => .ok entry.value state
        | none => .error (.missingKey key) state) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Abstraction.readDict_agrees state address profile table entries key query laws related admitted frozen cell

/-- A mutable canonical dictionary write reaches the exact related successor when the key observations stay coherent. -/
theorem writeDict_agrees (state : State) (address : Lists.Address) (profile : KeyProfile)
    (table : Table) (entries : List Entry) (key value : Value) (query : KeyObservation)
    (laws : Coherent state.heap profile) (related : Related state.heap profile table entries)
    (admitted : profile key = some query) (cell : state.heap[address]? = some ⟨.dict entries, false⟩)
    (inactive : address ∉ state.iterators) :
    let rows := putEntry ⟨key, query.code, value⟩ entries
    let after := { state with heap := state.heap.setIfInBounds address ⟨.dict rows, false⟩ }
    ∃ next, Deletion.set state.heap table key value = .ok next ∧
      writeDict address key value state = .ok () after ∧
      (Coherent after.heap profile → Related after.heap profile next rows) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Abstraction.writeDict_agrees state address profile table entries key value query laws related admitted cell inactive

end Silmaril.Languages.Starlark.Lists.GoDictionary.Abstraction
