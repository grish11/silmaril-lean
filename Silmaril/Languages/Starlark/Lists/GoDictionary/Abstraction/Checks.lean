module

import Silmaril.Languages.Starlark.Lists.GoDictionary.Abstraction.Thms
meta import Silmaril.Languages.Starlark.Lists.GoDictionary.Abstraction.Defs
meta import Silmaril.Languages.Starlark.Lists.Comparison.Defs

namespace Silmaril.Languages.Starlark.Lists.GoDictionary.Abstraction

deriving instance DecidableEq for Except

private def int (value : Int) : Value := .scalar (.int value)
private def float (bits : UInt64) : Value := .scalar (.float bits)
private def flag (value : Bool) : Value := .scalar (.bool value)

private def writeBoth (address : Lists.Address) (heapAndTable : State × Deletion.Table) (pair : Value × Value) :
    Option (State × Deletion.Table) :=
  let (state, table) := heapAndTable
  match writeDict address pair.1 pair.2 state, Deletion.set state.heap table pair.1 pair.2 with
  | .ok () after, .ok next => some (after, next)
  | _, _ => none

private def scalarFixture : Option Bool := do
  let initial ← match allocateDict [] {} with
    | .ok (.dict address) state => some (address, state)
    | _ => none
  let initialKeys := (List.range 9).map (fun n => int (Int.ofNat n)) ++
    [int 4294967296, flag false, float 0x7ff8000000000007, int 9007199254740993, float 0x4340000000000000]
  let updates := (initialKeys.zipIdx.map fun (key, index) => (key, int (Int.ofNat index))) ++
    [(float 0x8000000000000000, int 100), (float 0xfff8000000000015, int 101)]
  let (state, table) ← updates.foldlM (writeBoth initial.1) (initial.2, Deletion.Table.empty)
  let entries ← (Comparison.dictionaryEntries state.heap initial.1).toOption
  let queries := [float 0x8000000000000000, int 4294967296, flag false, flag true, float 0xfff8000000000015,
    int 9007199254740993, int 9007199254740992, int 42]
  let wanted := [some (int 100), some (int 9), some (int 10), none, some (int 101),
    some (int 12), some (int 13), none]
  let physical := queries.map fun key => lookupEntry state.heap scalarProfile table key
  let canonical := queries.map fun key => Comparison.lookupDictionary state.heap initial.1 key
  pure (decide (table.width = Growth.Width.two.double ∧ entries.map Entry.key = initialKeys ∧
      table.entries.map (observeRow scalarProfile) = entries.map some ∧
      physical.map Except.toOption = canonical.map Except.toOption ∧
      canonical.map (fun result => result.map (Option.map Entry.value)) = wanted.map Except.ok))

#guard scalarFixture = some true

private def nest (leaf : Value) : Meaning Value :=
  (List.range 10).foldlM (fun item _ => allocateTuple [item]) leaf

private def separatingFixture : Meaning (Lists.Address × Value × Value × Value) := do
  let stored ← nest (int 0)
  let alias ← nest (float 0x8000000000000000)
  let collision ← nest (int 4294967296)
  let receiver ← allocateDict []
  match receiver with
  | .dict address =>
    writeDict address stored (int 7)
    pure (address, stored, alias, collision)
  | _ => throw .assignmentTarget

-- A canonical tuple code can pick a hit or a miss before Go's bounded key
-- comparison can decide. Both physical lookups reach the same depth error.
#guard
  match separatingFixture {} with
  | .error .. => false
  | .ok (address, stored, alias, collision) state =>
    match Deletion.set state.heap Deletion.Table.empty stored (int 7) with
    | .error _ => false
    | .ok table =>
      decide ((Comparison.lookupDictionary state.heap address alias).map (Option.map Entry.key) = .ok (some stored) ∧
        Comparison.lookupDictionary state.heap address collision = .ok none ∧
        Deletion.get state.heap table alias = .error (.runtime .comparisonDepth) ∧
        Deletion.get state.heap table collision = .error (.runtime .comparisonDepth) ∧
        Deletion.contains state.heap table alias = .ok false)

end Silmaril.Languages.Starlark.Lists.GoDictionary.Abstraction
