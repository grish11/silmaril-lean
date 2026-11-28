module

public import Silmaril.Languages.Starlark.Lists.GoDictionary.Abstraction.Defs
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Abstraction.Lookup
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Abstraction.Assignment

public section

namespace Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Abstraction

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Lists (State Entry findEntry putEntry readDict writeDict)
open Silmaril.Languages.Starlark.Lists.GoDictionary.Abstraction
open Silmaril.Languages.Starlark.Lists.GoDictionary.Deletion (Table)

private theorem keyOf_heap (state : State) (key : Lists.Value) :
    state.keyOf key = ({ heap := state.heap } : State).keyOf key := by
  cases key <;> rfl

theorem readDict_agrees (state : State) (address : Lists.Address) (profile : KeyProfile)
    (table : Table) (entries : List Entry) (key : Lists.Value) (query : KeyObservation)
    (laws : Coherent state.heap profile) (related : Related state.heap profile table entries)
    (admitted : profile key = some query) (frozen : Bool)
    (cell : state.heap[address]? = some ⟨.dict entries, frozen⟩) :
    ∃ found, lookupEntry state.heap profile table key = .ok found ∧
      Lists.Comparison.lookupDictionary state.heap address key = .ok found ∧
      readDict address key state = (match found with
        | some entry => .ok entry.value state
        | none => .error (.missingKey key) state) := by
  have code := laws.canonical key query admitted
  refine ⟨findEntry query.code entries, lookup_agrees state.heap profile table entries key query laws related admitted,
    ?_, ?_⟩
  · simp [Lists.Comparison.lookupDictionary, Lists.Comparison.dictionaryEntries, cell, code,
      bind, Except.bind, pure, Except.pure]
  · simp [readDict, Lists.dictEntries, Lists.projectCell, Lists.getCell, cell, keyOf_heap state key, code,
      bind, EStateM.bind, pure, EStateM.pure] <;> rfl

theorem writeDict_agrees (state : State) (address : Lists.Address) (profile : KeyProfile)
    (table : Table) (entries : List Entry) (key value : Lists.Value) (query : KeyObservation)
    (laws : Coherent state.heap profile) (related : Related state.heap profile table entries)
    (admitted : profile key = some query) (cell : state.heap[address]? = some ⟨.dict entries, false⟩)
    (inactive : address ∉ state.iterators) :
    let rows := putEntry ⟨key, query.code, value⟩ entries
    let after := { state with heap := state.heap.setIfInBounds address ⟨.dict rows, false⟩ }
    ∃ next, Lists.GoDictionary.Deletion.set state.heap table key value = .ok next ∧
      writeDict address key value state = .ok () after ∧
      (Coherent after.heap profile → Related after.heap profile next rows) := by
  obtain ⟨next, ran, observed⟩ := set_agrees state.heap profile table entries key value query laws related admitted
  have code := laws.canonical key query admitted
  dsimp only
  refine ⟨next, ran, ?_, fun afterLaws => related_heap _ _ _ _ _ laws afterLaws observed⟩
  simp [writeDict, Lists.editCell, Lists.getCell, cell, inactive, keyOf_heap state key, code, bind,
    EStateM.bind, Except.bind, pure, Except.pure, Lists.Contents.sameMutableKind]

end Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Abstraction
