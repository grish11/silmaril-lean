module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Defs

/-! Move a final entry Store into the existing two-route overwrite check. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final

open Discovery.MemRef.CF (lowerDiamond)

variable {args : List ValueSort}

/-- Cut a nominated argument Store after checking its suffix. Preserve
the exact earlier memory operations and reindex the retained suffix. -/
def cutWith
    (check : PrefixStore args → {past : List (List ValueSort)} → {live : Nat} → Memory.Body args past live → Bool)
    (version : Nat) :
    {past : List (List ValueSort)} → {live : Nat} → Memory.Body args past live →
      Option (PrefixStore args × Memory.Body args past live)
  | _, _, .ret _ _ => none
  | _, _, .load memory address rest =>
    (cutWith check version rest).map fun (store, retainedEntry) => (store, .load memory address retainedEntry)
  | _, live, .store memory address word rest =>
    if live + 1 = version then
      match address, word with
      | .arg address, .arg word =>
        let selected : PrefixStore args := ⟨address, word⟩
        if check selected rest then
          some (selected, Memory.DeadStore.reindexMemory rest live)
        else none
      | _, _ => none
    else
      (cutWith check version rest).map fun (store, retainedEntry) => (store, .store memory address word retainedEntry)

/-- Remove the nominated one-based argument Store immediately before Return. -/
def cut (version : Nat) {past : List (List ValueSort)} {live : Nat} (body : Memory.Body args past live) :
    Option (PrefixStore args × Memory.Body args past live) :=
  cutWith (fun _ {_ _} tail => match tail with | .ret _ _ => true | _ => false) version body

/-- Reuse the static two-route check, with the retained entry table supplying
the heap to the selected arm. Both artifacts use the same typed inputs. -/
def lower (cells : Nat) (graph : Graph args) (entry : Memory.Graph args)
    (version : Nat) : Option (Artifacts cells args) := do
  let (store, retainedEntry) ← cut version entry
  let edited ← Static.rewrite ⟨store, graph⟩
  some ⟨lowerDiamond cells graph (some entry), lowerDiamond cells edited.graph (some retainedEntry)⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final
