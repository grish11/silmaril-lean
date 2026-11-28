module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.Defs

/-! Cut a Store fed by a retained entry binding before a finite MemRef switch. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord

open RVSDG (Port Tuple)
open Quads.CFG (Predecessors)
open DeadStore.Entry.Composition.Static.Final.LoadTail (checkTailAddress)
open Memory.Forwarding.Disjoint (Certificate)

variable {args : List ValueSort} {cells sites : Nat}

structure Cut (args : List ValueSort) (past : List (List ValueSort)) (live : Nat) where
  address : Port args .address
  /-- The exact retained prefix, returning the nominated Store's actual data wire. -/
  beforeStore : Memory.Body args past live
  retained : Memory.Body args past live

/-- Preserve the typed prefix up to the nominated Store in both outputs. The
retained entry reconnects the checked Load suffix to the earlier memory edge. -/
def cut (facts : Certificate args) (version : Nat) :
    {past : List (List ValueSort)} → {live : Nat} → Memory.Body args past live → Option (Cut args past live)
  | _, _, .ret _ _ => none
  | _, _, .load memory address rest =>
    (cut facts version rest).map fun edit =>
      ⟨edit.address, .load memory address edit.beforeStore, .load memory address edit.retained⟩
  | _, live, .store memory address word rest =>
    if live + 1 = version then
      match address, word with
      | .arg address, .output binding result =>
        if checkTailAddress facts address rest then
          some ⟨address, .ret memory (.output binding result), Memory.DeadStore.reindexMemory rest live⟩
        else none
      | _, _ => none
    else
      (cut facts version rest).map fun edit =>
        ⟨edit.address, .store memory address word edit.beforeStore, .store memory address word edit.retained⟩

/-- Use the native interval check on the original arm and its one-based Store
version. The overwritten word need not be an argument of the arm. -/
def checkArm (address : Port args .address) (arm : Memory.Graph args) (witness : ArmOverwrite args)
    (input : Tuple (Val cells) args) : Bool :=
  let facts : Certificate args := ⟨address, witness.readers⟩
  facts.check input && Memory.DeadStore.noReadUntil facts witness.storeVersion arm

def checkArms (preds : Predecessors sites) (address : Port args .address)
    (arm : Occurrence preds → Memory.Graph args) (candidate : Candidate args preds) (input : Tuple (Val cells) args) :
    Bool :=
  (List.finRange (preds.rest.length + 1)).all fun i => checkArm address (arm i) (candidate i) input

/-- A checked CFG pair together with the exact native entry edit used to emit it. -/
structure Emission (cells : Nat) (args : List ValueSort) (preds : Predecessors sites) where
  edit : Cut args [] 0
  programs : Programs cells args preds

/-- Check the suffix and each incoming occurrence at the same typed input,
and expose the retained entry for a subsequent check. -/
def lowerWithEntry (preds : Predecessors sites) (fits : Fits preds) (entry : Memory.Graph args) (version : Nat)
    (arm : Occurrence preds → Memory.Graph args) (candidate : Candidate args preds)
    (suffix : Memory.Graph (.word :: args)) (input : Tuple (Val cells) args)
    (facts : Certificate args) : Option (Emission cells args preds) := do
  let edit ← cut facts version entry
  if facts.check input && checkArms preds edit.address arm candidate input then
    some ⟨edit, input, lowerBank preds fits cells (some entry) arm suffix,
      lowerBank preds fits cells (some edit.retained) arm suffix⟩
  else none

/-- Check the suffix and each incoming occurrence at the same typed input.
Only the entry changes in the actual pair of MemRef CFGs. -/
def lower (preds : Predecessors sites) (fits : Fits preds) (entry : Memory.Graph args) (version : Nat)
    (arm : Occurrence preds → Memory.Graph args) (candidate : Candidate args preds)
    (suffix : Memory.Graph (.word :: args)) (input : Tuple (Val cells) args)
    (facts : Certificate args) : Option (Programs cells args preds) := do
  let edit ← cut facts version entry
  if facts.check input && checkArms preds edit.address arm candidate input then
    some ⟨input, lowerBank preds fits cells (some entry) arm suffix,
      lowerBank preds fits cells (some edit.retained) arm suffix⟩
  else none

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord
