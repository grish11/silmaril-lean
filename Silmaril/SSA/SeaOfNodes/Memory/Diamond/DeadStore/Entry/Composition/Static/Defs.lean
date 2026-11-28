module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Defs

/-! A same-port two-route Store cut independent of the invocation. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static

open SeaOfNodes.Diamond (Slot)
open Discovery.MemRef.CF (Program lowerDiamond)

variable {args : List ValueSort}

/-- Use the existing path checker with the discovered overwrite and
reader certificate for this occurrence. -/
def rewriteSlot (source : Prefixed args) (candidate : Candidate args) (arrival : Slot) :
    Option (Memory.Graph args) :=
  let witness := candidate arrival
  let arm := source.diamond.arm (source.diamond.merge.predecessor arrival)
  Memory.DeadStore.rewriteWith (source.store.prepend arm) ⟨1, witness.storeVersion + 1⟩
    ⟨source.store.address, witness.readers⟩

/-- Both routes must have empty reader obligations. The static path
checker requires the overwrite to use the nominated Store's typed port. -/
def rewriteWith (source : Prefixed args) (candidate : Candidate args) : Option (Graph args) :=
  if (candidate .first).readers.isEmpty && (candidate .second).readers.isEmpty then
    DeadStore.rewriteUsing source (rewriteSlot source candidate)
  else none

/-- Discover the overwrite witnesses independently at the two Region slots. -/
def rewrite (source : Prefixed args) : Option (Discovery.Result args) := do
  let candidate ← Discovery.discover source
  (rewriteWith source candidate).map (Discovery.Result.mk candidate)

structure Artifacts (cells : Nat) (args : List ValueSort) where
  original : Program cells args
  optimized : Program cells args

/-- Emit a singleton entry Store cut and its original diamond. The same
artifacts can run at any typed valuation. -/
def lower (cells : Nat) (graph : Graph args) (entry : Memory.Graph args) : Option (Artifacts cells args) := do
  let store ← Composition.asPrefixStore entry
  let edited ← rewrite ⟨store, graph⟩
  some ⟨lowerDiamond cells graph (some entry), lowerDiamond cells edited.graph none⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static
