module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Defs

/-! Check the ordered Load and Store suffix after the nominated entry Store. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load

open RVSDG (Tuple)
open Memory.Forwarding.Disjoint (cell)
open Discovery.MemRef.CF (lowerDiamond)

variable {args : List ValueSort} {cells : Nat}

/-- Check every suffix memory operation at the supplied scalar input.
Only original address arguments are admitted. Store data and Return may
use any in-scope word, including the result of a retained Load. -/
def checkTail (selected : PrefixStore args) (input : Tuple (Val cells) args) :
    {past : List (List ValueSort)} → {live : Nat} → Memory.Body args past live → Bool
  | _, _, .ret _ _ => true
  | _, _, .load _ (.arg reader) rest =>
    decide (cell input selected.address ≠ cell input reader) && checkTail selected input rest
  | _, _, .store _ (.arg writer) _ rest =>
    decide (cell input selected.address ≠ cell input writer) && checkTail selected input rest
  | _, _, _ => false

/-- Find the first later Store to the nominated cell. Every Load before it
must read another cell. Before and at the overwrite, addresses must be
original arguments. After the overwrite the complete states agree. -/
def checkOverwrite (selected : PrefixStore args) (input : Tuple (Val cells) args) :
    {past : List (List ValueSort)} → {live : Nat} → Memory.Body args past live → Bool
  | _, _, .load _ (.arg reader) rest =>
    decide (cell input selected.address ≠ cell input reader) && checkOverwrite selected input rest
  | _, _, .store _ (.arg writer) _ rest =>
    if cell input selected.address = cell input writer then true
    else checkOverwrite selected input rest
  | _, _, _ => false

/-- Cut one one-based Store version after an argument-Store prefix using
the supplied tail check. Reconnect memory edges without changing scalar origins. -/
def cutWith
    (check : PrefixStore args → {past : List (List ValueSort)} → {live : Nat} → Memory.Body args past live → Bool)
    (version : Nat) :
    {past : List (List ValueSort)} → {live : Nat} → Memory.Body args past live →
      Option (PrefixStore args × Memory.Body args past live)
  | _, live, .store memory (.arg address) (.arg word) rest =>
    if live + 1 = version then
      let selected : PrefixStore args := ⟨address, word⟩
      if check selected rest then
        some (selected, Memory.DeadStore.reindexMemory rest live)
      else none
    else (cutWith check version rest).map fun (selected, tail) =>
      (selected, .store memory (.arg address) (.arg word) tail)
  | _, _, _ => none

/-- Cut the nominated Store when the entire tail is disjoint from its cell. -/
def cut (version : Nat) (input : Tuple (Val cells) args)
    {past : List (List ValueSort)} {live : Nat} (body : Memory.Body args past live) :
    Option (PrefixStore args × Memory.Body args past live) :=
  cutWith (fun selected {_ _} tail => checkTail selected input tail) version body

/-- Cut the nominated Store when the tail overwrites its cell before observing it. -/
def cutOverwrite (version : Nat) (input : Tuple (Val cells) args)
    {past : List (List ValueSort)} {live : Nat} (body : Memory.Body args past live) :
    Option (PrefixStore args × Memory.Body args past live) :=
  cutWith (fun selected {_ _} tail => checkOverwrite selected input tail) version body

def rewrite (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args) : Option (Retained.Edit args) := do
  let (selected, retained) ← cut version input entry
  (Discovery.rewrite ⟨selected, graph⟩ input).map (Retained.Edit.mk retained)

/-- Refusal of the tail or either route keeps the entry-local result. -/
def lower (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args) : Composition.Result cells args :=
  let repeated := Entry.lowerRepeated graph entry input
  match rewrite graph repeated.entry version input with
  | none => ⟨repeated.deleted, false, repeated.programs⟩
  | some edit => ⟨repeated.deleted, true, { repeated.programs with
      optimized := lowerDiamond cells edit.routes.graph (some edit.retained) }⟩

structure OverwriteResult (cells : Nat) (args : List ValueSort) where
  entryDeleted : Nat
  overwriteDeleted : Bool
  programs : Discovery.MemRef.CF.Programs cells args

/-- Run entry-local cleanup, then try a one-based nomination on the current
table. Success changes only the entry. Refusal keeps the initial cleanup. -/
def lowerOverwrite (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args) : OverwriteResult cells args :=
  let repeated := Entry.lowerRepeated graph entry input
  match cutOverwrite version input repeated.entry with
  | none => ⟨repeated.deleted, false, repeated.programs⟩
  | some (_, retained) => ⟨repeated.deleted, true, Entry.lowerPair graph entry retained input⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load
