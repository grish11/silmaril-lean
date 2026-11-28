module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Reindex.Defs

/-! Check explicit sequences of static Store cuts on the native diamond entry. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence

open RVSDG (Tuple)
open Diamond.Institution (PortMap)

variable {args target : List ValueSort} {cells : Nat}

structure Step (args : List ValueSort) where
  /-- The one-based version in the table produced by the preceding steps. -/
  version : Nat
  facts : AddressContract args

abbrev Plan (args : List ValueSort) := List (Step args)

/-- Every structural check receives the current entry. Any refusal
discards the entire result. -/
def Plan.rewrite (plan : Plan args) (entry : Memory.Graph args) : Option (Memory.Graph args) :=
  plan.foldlM (fun current step => (Static.cut step.facts step.version current).map Prod.snd) entry

def Plan.Valid (plan : Plan args) (input : Tuple (Val cells) args) : Prop :=
  ∀ step ∈ plan, step.facts.Valid input

def Plan.check (plan : Plan args) (input : Tuple (Val cells) args) : Bool :=
  plan.all (fun step => step.facts.check input)

def Step.transport (step : Step args) (rename : PortMap args target) : Option (Step target) :=
  (step.facts.transport rename).map (Step.mk step.version)

/-- Preserve the step order and versions, or refuse any inconsistent transport. -/
def Plan.transport (plan : Plan args) (rename : PortMap args target) : Option (Plan target) :=
  plan.mapM (fun step => step.transport rename)

/-- Check every contract at this invocation and emit only the original and
the completed final table. A failing step or contract gives no program pair. -/
def lower (graph : Graph args) (entry : Memory.Graph args) (plan : Plan args)
    (input : Tuple (Val cells) args) : Option (Discovery.MemRef.CF.Programs cells args) :=
  if plan.check input then
    (plan.rewrite entry).map (fun final => Entry.lowerPair graph entry final input)
  else none

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence
