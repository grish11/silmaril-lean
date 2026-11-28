module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Replay.Defs

/-! Discover checked cuts on the current finite switch entry. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Replay.Search

open RVSDG (Port Tuple)
open Quads.CFG (Predecessors)
open Memory.Forwarding.Disjoint (Certificate)
open Memory.DeadStore.Search (findOverwrite)
open Memory.DeadStore.Search.Selection (storeVersions)
open Memory.DeadStore.Search.Selection.Readers.discover (beforeOverwrite)
open Memory.DeadStore.Search.Selection.Readers.Repeat (storeCount)
open DeadStore.Entry.Composition.Static.Final.LoadTail (readPorts)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}

/-- Read a nominated Store's original address and the typed readers after it.
A suffix with a Store cannot enter the trailing-Load profile. -/
def inferEntry (version : Nat) :
    {past : List (List ValueSort)} → {live : Nat} → Memory.Body args past live → Option (Certificate args)
  | _, _, .ret _ _ => none
  | _, _, .load _ _ rest => inferEntry version rest
  | _, live, .store _ address _ rest =>
    if live + 1 = version then
      match address with
      | .arg port => (readPorts rest).map (Certificate.mk port)
      | .output _ _ => none
    else inferEntry version rest

/-- Reuse the native straight-line reader and overwrite searches on each
original occurrence independently, even when predecessor IDs repeat. -/
def inferCandidate (preds : Predecessors sites) (address : Port args .address)
    (arm : Occurrence preds → Memory.Graph args) : Option (Candidate args preds) := do
  let witnesses ← Vector.ofFnM fun (i : Occurrence preds) => do
    let readers ← beforeOverwrite address (arm i)
    let overwrite ← findOverwrite ⟨address, readers⟩ (arm i)
    some (⟨overwrite, readers⟩ : ArmOverwrite args)
  some fun i => witnesses[i.val]

/-- The generated facts are proposals. Admission still uses the typed cut,
concrete cell inequalities and all occurrence checks at the saved input. -/
def tryVersion (fits : Fits preds) (arm : Occurrence preds → Memory.Graph args)
    (suffix : Memory.Graph (.word :: args)) (input : Tuple (Val cells) args)
    (entry : Memory.Graph args) (version : Nat) : Option (Request args preds × Emission cells args preds) := do
  let facts ← inferEntry version entry
  let candidate ← inferCandidate preds facts.observed arm
  let stage ← lowerWithEntry preds fits entry version arm candidate suffix input facts
  some (⟨version, facts, candidate⟩, stage)

/-- Scan the actual surviving Store versions in ascending table order.
A refused version advances the scan. -/
def find (fits : Fits preds) (arm : Occurrence preds → Memory.Graph args)
    (suffix : Memory.Graph (.word :: args)) (input : Tuple (Val cells) args) (entry : Memory.Graph args) :
    Option (Request args preds × Emission cells args preds) :=
  (storeVersions entry).findSome? (tryVersion fits arm suffix input entry)

structure Result (cells : Nat) (args : List ValueSort) (preds : Predecessors sites) where
  requests : List (Request args preds)
  replay : Replay.Result cells args preds

/-- After an acceptance, restart on the actual retained entry. The
emissions are returned directly, so the pass never needs a second emit. -/
def run (fits : Fits preds) (arm : Occurrence preds → Memory.Graph args) (suffix : Memory.Graph (.word :: args))
    (input : Tuple (Val cells) args) :
    Nat → Memory.Graph args → Program cells args preds → Result cells args preds
  | 0, entry, current => ⟨[], .stop input entry current []⟩
  | fuel + 1, entry, current =>
    match find fits arm suffix input entry with
    | none => ⟨[], .stop input entry current []⟩
    | some (request, stage) =>
      let rest := run fits arm suffix input fuel stage.edit.retained stage.programs.optimized
      ⟨request :: rest.requests, rest.replay.prepend input current stage⟩

/-- The original Store count bounds the number of successful iterations. -/
def lower (preds : Predecessors sites) (fits : Fits preds) (entry : Memory.Graph args)
    (arm : Occurrence preds → Memory.Graph args) (suffix : Memory.Graph (.word :: args))
    (input : Tuple (Val cells) args) : Result cells args preds :=
  run fits arm suffix input (storeCount entry) entry (lowerBank preds fits cells (some entry) arm suffix)

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Replay.Search
