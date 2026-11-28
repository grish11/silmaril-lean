module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Replay.Search.Defs

/-! Discover one finite-switch Store cut across an independent mixed entry suffix. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail

open RVSDG (Port Tuple)
open Quads.CFG (Predecessors)
open Memory.Forwarding.Disjoint (Certificate)
open Memory.DeadStore.Search.Selection (storeVersions)
open LoadTail.PrefixWord.Sequence.Replay.Search (inferCandidate)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}

/-- List every retained access in order. Store data may use any in-scope word. -/
def tailPorts :
    {past : List (List ValueSort)} → {live : Nat} → Memory.Body args past live → Option (List (Port args .address))
  | _, _, .ret _ _ => some []
  | _, _, .load _ (.arg address) rest => (tailPorts rest).map (address :: ·)
  | _, _, .store _ (.arg address) _ rest => (tailPorts rest).map (address :: ·)
  | _, _, _ => none

/-- Expose the exact prefix readback and rethread the retained memory
edge, keeping the original scalar operands and all suffix accesses. -/
def inferCut (version : Nat) :
    {past : List (List ValueSort)} → {live : Nat} → Memory.Body args past live →
      Option (LoadTail.PrefixWord.Cut args past live × List (Port args .address))
  | _, _, .ret _ _ => none
  | _, _, .load memory address rest =>
    (inferCut version rest).map fun (edit, ports) =>
      (⟨edit.address, .load memory address edit.beforeStore, .load memory address edit.retained⟩, ports)
  | _, live, .store memory address word rest =>
    if live + 1 = version then
      match address, word with
      | .arg address, .output binding result =>
        (tailPorts rest).map fun ports =>
          (⟨address, .ret memory (.output binding result), Memory.DeadStore.reindexMemory rest live⟩, ports)
      | _, _ => none
    else
      (inferCut version rest).map fun (edit, ports) =>
        (⟨edit.address, .store memory address word edit.beforeStore, .store memory address word edit.retained⟩, ports)

structure Result (cells : Nat) (args : List ValueSort) (preds : Predecessors sites) where
  version : Nat
  ports : List (Port args .address)
  candidate : Candidate args preds
  emission : LoadTail.PrefixWord.Emission cells args preds

def Result.facts (result : Result cells args preds) : Certificate args :=
  ⟨result.emission.edit.address, result.ports⟩

/-- Require concrete separation for every suffix access and independently
check each original arm's overwrite before emitting the actual pair. -/
def tryVersion (fits : Fits preds) (arm : Occurrence preds → Memory.Graph args)
    (suffix : Memory.Graph (.word :: args)) (input : Tuple (Val cells) args)
    (entry : Memory.Graph args) (version : Nat) : Option (Result cells args preds) := do
  let (edit, ports) ← inferCut version entry
  let candidate ← inferCandidate preds edit.address arm
  let facts : Certificate args := ⟨edit.address, ports⟩
  if facts.check input && LoadTail.PrefixWord.checkArms preds edit.address arm candidate input then
    some ⟨version, ports, candidate,
      ⟨edit, ⟨input, lowerBank preds fits cells (some entry) arm suffix,
        lowerBank preds fits cells (some edit.retained) arm suffix⟩⟩⟩
  else none

/-- Try the actual Store versions oldest first, allowing a nonfinal
nomination when every retained suffix access is independent. -/
def lower (fits : Fits preds) (arm : Occurrence preds → Memory.Graph args)
    (suffix : Memory.Graph (.word :: args)) (input : Tuple (Val cells) args)
    (entry : Memory.Graph args) : Option (Result cells args preds) :=
  (storeVersions entry).findSome? (tryVersion fits arm suffix input entry)

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail
