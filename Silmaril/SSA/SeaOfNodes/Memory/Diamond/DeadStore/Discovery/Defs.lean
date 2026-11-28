module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Defs

/-! Discover the common entry Store's overwrite and reader obligations on both occurrences. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery

open RVSDG (Tuple)
open SeaOfNodes.Diamond (Slot)
open Memory.DeadStore.Search.Selection.Readers renaming discover → discoverReaders

variable {args : List ValueSort} {cells : Nat}

/-- Inspect the actual incoming path through the existing straight-line
reader and overwrite searches. The prepended Store occupies version one. -/
def discoverSlot (source : Prefixed args) (arrival : Slot) : Option (ArmOverwrite args) := do
  let arm := source.diamond.arm (source.diamond.merge.predecessor arrival)
  let path := source.store.prepend arm
  let facts ← discoverReaders path 1
  let pair ← Memory.DeadStore.Search.discover path 1 facts
  some ⟨pair.overwriteVersion - 1, facts.writers⟩

/-- Collect one set of reader obligations for each Region occurrence. -/
def discover (source : Prefixed args) : Option (Candidate args) := do
  let first ← discoverSlot source .first
  let second ← discoverSlot source .second
  some fun
    | .first => first
    | .second => second

structure Result (args : List ValueSort) where
  candidate : Candidate args
  graph : Graph args

/-- Require the original two-route checker to validate the discovered
candidate at the same typed scalar input for both routes. -/
def rewrite (source : Prefixed args) (input : Tuple (Val cells) args) : Option (Result args) := do
  let candidate ← discover source
  let graph ← DeadStore.rewrite source candidate input
  some ⟨candidate, graph⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery
