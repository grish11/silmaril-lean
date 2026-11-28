module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Defs

/-! Reuse a checked mixed cut under its original typed address obligations. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse

open RVSDG (Tuple)
open Quads.CFG (Predecessors)
open Entry.Composition.Retained.Load.Static (AddressContract)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}

/-- The entry access obligations and the original occurrence bank's reader
obligations. Each slot retains its own certificate in predecessor order. -/
structure Contract (args : List ValueSort) (preds : Predecessors sites) where
  entry : AddressContract args
  arms : Vector (AddressContract args) (preds.rest.length + 1)

def Contract.Valid (facts : Contract args preds) (input : Tuple (Val cells) args) : Prop :=
  facts.entry.Valid input ∧ ∀ i : Occurrence preds, facts.arms[i.val].Valid input

def Contract.check (facts : Contract args preds) (input : Tuple (Val cells) args) : Bool :=
  facts.entry.check input &&
    (List.finRange (preds.rest.length + 1)).all (fun i => facts.arms[i.val].check input)

/-- The overwrite's must-alias is already enforced by the same typed port.
Collect the concrete separation obligations without reading scalar values. -/
def contractOf (stage : MixedTail.Result cells args preds) : Contract args preds :=
  ⟨⟨stage.facts, []⟩, Vector.ofFn (fun i =>
    ⟨⟨stage.emission.edit.address, (stage.candidate i).readers⟩, []⟩)⟩

/-- Bind a new invocation to the exact same source and optimized programs. -/
def atInput (stage : MixedTail.Result cells args preds) (input : Tuple (Val cells) args) :
    MixedTail.Result cells args preds :=
  { stage with emission := { stage.emission with programs := { stage.emission.programs with input := input } } }

/-- For an admitted cut, validate its contract at the new input before
returning the same emitted pair with the updated invocation. -/
def reuse (stage : MixedTail.Result cells args preds) (input : Tuple (Val cells) args) :
    Option (MixedTail.Result cells args preds) :=
  if (contractOf stage).check input then some (atInput stage input) else none

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse
