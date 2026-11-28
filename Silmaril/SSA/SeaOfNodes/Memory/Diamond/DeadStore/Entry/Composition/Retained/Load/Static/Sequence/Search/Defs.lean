module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Defs

/-! Discover static entry cuts using the caller's typed address contracts. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Search

open RVSDG (Tuple)
open Memory.DeadStore.Search.Selection (storeVersions)
open Memory.DeadStore.Search.Selection.Readers.Repeat (storeCount)

variable {args : List ValueSort} {cells : Nat}

def ContractsValid (contracts : List (AddressContract args)) (input : Tuple (Val cells) args) : Prop :=
  ∀ facts ∈ contracts, facts.Valid input

def checkContracts (contracts : List (AddressContract args)) (input : Tuple (Val cells) args) : Bool :=
  contracts.all (fun facts => facts.check input)

/-- Try the current Store versions in ascending table order. Break ties by
the supplied contract list order, using the existing static cut checker. -/
def find (entry : Memory.Graph args) (contracts : List (AddressContract args)) :
    Option (Step args × Memory.Graph args) :=
  (storeVersions entry).findSome? fun version =>
    contracts.findSome? fun facts =>
      (Static.cut facts version entry).map fun (_, retained) => (⟨version, facts⟩, retained)

structure Result (args : List ValueSort) where
  plan : Plan args
  entry : Memory.Graph args

/-- Each successful step records its version in the current table and
restarts discovery on the table produced by that step. -/
def run (contracts : List (AddressContract args)) : Nat → Memory.Graph args → Result args
  | 0, entry => ⟨[], entry⟩
  | fuel + 1, entry =>
    match find entry contracts with
    | none => ⟨[], entry⟩
    | some (step, retained) =>
      let rest := run contracts fuel retained
      ⟨step :: rest.plan, rest.entry⟩

/-- The original Store count bounds all accepted deletions. -/
def discover (entry : Memory.Graph args) (contracts : List (AddressContract args)) : Result args :=
  run contracts (storeCount entry) entry

inductive InvocationError where
  | invalidContracts

structure Emission (cells : Nat) (args : List ValueSort) extends Result args where
  programs : Discovery.MemRef.CF.Programs cells args

/-- Invalid invocation facts give an error. A valid invocation with no
eligible cut succeeds with an empty plan and an unchanged entry. -/
def lower (graph : Graph args) (entry : Memory.Graph args) (contracts : List (AddressContract args))
    (input : Tuple (Val cells) args) : Except InvocationError (Emission cells args) :=
  if checkContracts contracts input then
    let result := discover entry contracts
    .ok ⟨result, Entry.lowerPair graph entry result.entry input⟩
  else .error .invalidContracts

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Search
