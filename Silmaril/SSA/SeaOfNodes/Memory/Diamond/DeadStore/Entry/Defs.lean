module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Defs

/-! Checked Store deletion in a native diamond entry table. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry

open RVSDG (Tuple)
open Memory.DeadStore.Search.Selection (storeVersions)
open Memory.DeadStore.Search.Selection.Readers renaming discover → discoverReaders

variable {args : List ValueSort} {cells : Nat}

/-- Require the second Store to overwrite the first on its original address
wire. The existing checker validates the intervening Loads at this input. -/
def rewrite (entry : Memory.Graph args) (input : Tuple (Val cells) args) : Option (Memory.Graph args) :=
  if (storeVersions entry).length = 2 then do
    let facts ← discoverReaders entry 1
    Memory.DeadStore.rewrite entry ⟨1, 2⟩ facts input
  else none

/-- Emit both entry tables with the same diamond and scalar input. -/
def lowerPair (graph : Graph args) (entry edited : Memory.Graph args) (input : Tuple (Val cells) args) :
    Discovery.MemRef.CF.Programs cells args :=
  ⟨input, Discovery.MemRef.CF.lowerDiamond cells graph (some entry),
    Discovery.MemRef.CF.lowerDiamond cells graph (some edited)⟩

def lower (graph : Graph args) (entry : Memory.Graph args) (input : Tuple (Val cells) args) :
    Option (Discovery.MemRef.CF.Programs cells args) :=
  (rewrite entry input).map fun edited => lowerPair graph entry edited input

/-- Nominate the original one-based Store version to remove. Discover the
first same-wire overwrite and check every intervening Load at this input. -/
def rewriteSelected (entry : Memory.Graph args) (removeVersion : Nat) (input : Tuple (Val cells) args) :
    Option (Memory.DeadStore.Search.Selection.Result args) := do
  let facts ← discoverReaders entry removeVersion
  Memory.DeadStore.Search.Selection.tryStore entry input removeVersion facts

def lowerSelected (graph : Graph args) (entry : Memory.Graph args) (removeVersion : Nat)
    (input : Tuple (Val cells) args) : Option (Discovery.MemRef.CF.Programs cells args) :=
  (rewriteSelected entry removeVersion input).map fun result => lowerPair graph entry result.graph input

structure Repeated (cells : Nat) (args : List ValueSort) where
  entry : Memory.Graph args
  deleted : Nat
  programs : Discovery.MemRef.CF.Programs cells args

/-- Run the native repeat pass on the entry and lower its final table.
When the selector makes no further deletion, keep the current entry. -/
def lowerRepeated (graph : Graph args) (entry : Memory.Graph args) (input : Tuple (Val cells) args) :
    Repeated cells args :=
  let result := Memory.DeadStore.Search.Selection.Readers.Repeat.rewrite entry input
  ⟨result.graph, result.deleted, lowerPair graph entry result.graph input⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry
