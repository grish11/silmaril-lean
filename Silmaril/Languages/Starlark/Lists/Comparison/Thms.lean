module

public import Silmaril.Languages.Starlark.Lists.Comparison.Operational.Defs
import Silmaril.Proofs.Languages.Starlark.Lists.Comparison.Agreement

public section

namespace Silmaril.Languages.Starlark.Lists.Comparison

/-- Transfer ordered scans from a relational test to its exact result function. -/
theorem scans_iff_scan {α : Type} {tests : α → Except Error Bool → Prop}
    {test : α → Except Error Bool} (agrees : ∀ item out, tests item out ↔ test item = out)
    (decisive : Bool) (items : List α) (out : Except Error Bool) :
    Scans tests decisive items out ↔ scan test decisive items = out :=
  Proofs.Languages.Starlark.Lists.Comparison.scans_iff_scan agrees decisive items out

theorem looksUp_iff_findEntry (key : Key) (entries : List Entry) (out : Option Entry) :
    LooksUp key entries out ↔ findEntry key entries = out :=
  Proofs.Languages.Starlark.Lists.Comparison.looksUp_iff_findEntry key entries out

theorem dictionaryLookup_iff (heap : Heap) (address : Address) (key : Value)
    (out : Except Error (Option Entry)) :
    DictionaryLookup heap address key out ↔ lookupDictionary heap address key = out :=
  Proofs.Languages.Starlark.Lists.Comparison.dictionaryLookup_iff heap address key out

theorem probes_iff_probe {α : Type} {tests : α → Except Error Bool → Prop}
    {test : α → Except Error Bool} (agree : ∀ item out, tests item out ↔ test item = out)
    (candidates : List α) (out : Except Error (Option α)) :
    Probes tests candidates out ↔ probe test candidates = out :=
  Proofs.Languages.Starlark.Lists.Comparison.probes_iff_probe agree candidates out

/-- A total canonical code test specializes the ordered probe to normal lookup. -/
theorem probe_cached (key : Key) (entries : List Entry) :
    probe (fun entry : Entry => .ok (entry.keyCode == key)) entries = .ok (findEntry key entries) :=
  Proofs.Languages.Starlark.Lists.Comparison.probe_cached key entries

theorem lookupOrMiss_some_iff {α : Type} (out : Except Error (Option α)) (value : α) :
    lookupOrMiss out = some value ↔ out = .ok (some value) := by
  cases out <;> simp [lookupOrMiss]

/-- In a valid table, a key selects its entry regardless of insertion position. -/
theorem findEntry_some_iff_of_unique (key : Key) (entries : List Entry) (entry : Entry)
    (unique : UniqueKeyCodes entries) :
    findEntry key entries = some entry ↔ entry ∈ entries ∧ entry.keyCode = key :=
  Proofs.Languages.Starlark.Lists.Comparison.findEntry_some_iff_of_unique key entries entry unique

/-- The dictionary display's checked append preserves unique key codes. -/
theorem uniqueKeyCodes_append_of_missing (entry : Entry) (entries : List Entry)
    (unique : UniqueKeyCodes entries) (missing : findEntry entry.keyCode entries = none) :
    UniqueKeyCodes (entries ++ [entry]) :=
  Proofs.Languages.Starlark.Lists.Comparison.uniqueKeyCodes_append_of_missing entry entries unique missing

/-- Dictionary assignment preserves unique key codes on both replacement and insertion. -/
theorem uniqueKeyCodes_putEntry (entry : Entry) (entries : List Entry)
    (unique : UniqueKeyCodes entries) : UniqueKeyCodes (putEntry entry entries) :=
  Proofs.Languages.Starlark.Lists.Comparison.uniqueKeyCodes_putEntry entry entries unique

theorem equalAt_iff (heap : Heap) (depth : Nat) (left right : Value)
    (out : Except Error Bool) :
    EqualAt heap depth left right out ↔ equalAt heap depth left right = out :=
  Proofs.Languages.Starlark.Lists.Comparison.equalAt_iff heap depth left right out

/-- Agreement for bounded key equality on an already selected candidate order. -/
theorem probesKeys_iff (heap : Heap) (depth : Nat) (key : Value) (candidates : List Entry)
    (out : Except Error (Option Entry)) :
    Probes (fun entry => EqualAt heap depth key entry.key) candidates out ↔
      probeKeys heap depth key candidates = out :=
  probes_iff_probe (fun entry => equalAt_iff heap depth key entry.key) candidates out

theorem containsAt_iff (heap : Heap) (depth : Nat) (needle target : Value)
    (out : Except Error Bool) :
    ContainsAt heap depth needle target out ↔ containsAt heap depth needle target = out :=
  Proofs.Languages.Starlark.Lists.Comparison.containsAt_iff heap depth needle target out

theorem tests_iff_evaluate (heap : Heap) (left right : Value) (op : ComparisonOp)
    (out : Except Error Bool) :
    Tests heap left right op out ↔ evaluate heap op left right = out :=
  Proofs.Languages.Starlark.Lists.Comparison.tests_iff_evaluate heap left right op out

end Silmaril.Languages.Starlark.Lists.Comparison
