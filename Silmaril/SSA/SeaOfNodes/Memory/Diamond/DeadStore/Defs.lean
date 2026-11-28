module

public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Defs

/-! # Delete a common Store overwritten on both occurrences -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore

open RVSDG (Port Tuple)
open SeaOfNodes.Diamond (Slot)

variable {args : List ValueSort} {cells : Nat}

structure PrefixStore (args : List ValueSort) where
  address : Port args .address
  value : Port args .word

/-- Execute the entry Store in the native memory model. Its boundary exports
the memory version that enters the diamond. -/
def PrefixStore.table (store : PrefixStore args) : Memory.Graph args :=
  .store (.latest 0) (.arg store.address) (.arg store.value) (.ret (.latest 1) (.arg store.value))

/-- Form the native straight-line table for the entry Store followed by one arm. -/
def PrefixStore.prepend (store : PrefixStore args) (arm : Memory.Graph args) : Memory.Graph args :=
  .store (.latest 0) (.arg store.address) (.arg store.value) (Memory.DeadStore.reindexMemory arm 1)

/-- One entry Store and an ordinary memory diamond with an evaluated guard. -/
structure Prefixed (args : List ValueSort) where
  store : PrefixStore args
  diamond : Graph args

def Prefixed.Returns (source : Prefixed args) (guard : Bool) (input : Tuple (Val cells) args)
    (initial : Heap cells) (word : Word) (final : Heap cells) : Prop :=
  ∃ entryWord entryHeap, source.store.table.Returns input initial entryWord entryHeap ∧
    source.diamond.Returns guard input entryHeap word final

def Prefixed.denote (source : Prefixed args) (guard : Bool) (input : Tuple (Val cells) args)
    (initial : Heap cells) : Word × Heap cells :=
  source.diamond.denote guard input (source.store.table.denote input initial).2

structure ArmOverwrite (args : List ValueSort) where
  /-- The one-based Store version within this original arm. -/
  storeVersion : Nat
  readers : List (Port args .address)

/-- Each Region input occurrence has its own overwrite and reader evidence. -/
abbrev Candidate (args : List ValueSort) := Slot → ArmOverwrite args

/-- Check one closed path from the common entry Store to its export. -/
def rewriteArm (store : PrefixStore args) (arm : Memory.Graph args) (witness : ArmOverwrite args)
    (input : Tuple (Val cells) args) : Option (Memory.Graph args) :=
  Memory.DeadStore.rewrite (store.prepend arm) ⟨1, witness.storeVersion + 1⟩
    ⟨store.address, witness.readers⟩ input

def rewriteSlot (source : Prefixed args) (candidate : Candidate args) (input : Tuple (Val cells) args)
    (arrival : Slot) : Option (Memory.Graph args) :=
  rewriteArm source.store (source.diamond.arm (source.diamond.merge.predecessor arrival)) (candidate arrival) input

/-- Assemble the two accepted arm tables in their original Region slots. -/
def rewriteUsing (source : Prefixed args) (check : Slot → Option (Memory.Graph args)) :
    Option (Graph args) := do
  let first ← check .first
  let second ← check .second
  some { source.diamond with
    arm := fun edge => match source.diamond.merge.slot edge with
      | .first => first
      | .second => second }

/-- Require the checked deletion on both Region occurrences. The target
has no entry Store and runs the selected rewritten arm and original suffix. -/
def rewrite (source : Prefixed args) (candidate : Candidate args) (input : Tuple (Val cells) args) :
    Option (Graph args) :=
  rewriteUsing source (rewriteSlot source candidate input)

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore
