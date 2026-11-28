module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Defs

/-! A valuation-independent diamond entry edit under typed address facts. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static

open RVSDG (Port Tuple)
open Memory.Forwarding.Disjoint (Certificate cell)
open Discovery.MemRef.CF (Program lowerDiamond)

variable {args : List ValueSort} {cells : Nat}

/-- Facts relative to the nominated Store's original address argument.
Each listed alias denotes its cell. Each port in the existing disjointness
certificate denotes a different cell. -/
structure AddressContract (args : List ValueSort) where
  disjoint : Certificate args
  aliases : List (Port args .address)

def AddressContract.Valid (facts : AddressContract args) (input : Tuple (Val cells) args) : Prop :=
  facts.disjoint.Valid input ∧
    ∀ port ∈ facts.aliases, cell input facts.disjoint.observed = cell input port

/-- Validate the facts for a particular run of an already emitted artifact. -/
def AddressContract.check (facts : AddressContract args) (input : Tuple (Val cells) args) : Bool :=
  facts.disjoint.check input &&
    facts.aliases.all (fun port => decide (cell input facts.disjoint.observed = cell input port))

def AddressContract.same (facts : AddressContract args) (port : Port args .address) : Bool :=
  facts.disjoint.matches (past := []) (.arg port) || facts.aliases.any (fun other => port.index == other.index)

/-- Reject a disjointness fact about a known alias, including the anchor itself. -/
def AddressContract.consistent (facts : AddressContract args) : Bool :=
  facts.disjoint.writers.all (fun port => !facts.same port)

/-- Follow only certified disjoint accesses until the first certified
same-cell Store. An unclassified access refuses the edit. -/
def checkTail (facts : AddressContract args) :
    {past : List (List ValueSort)} → {live : Nat} → Memory.Body args past live → Bool
  | _, _, .load _ (.arg reader) rest => facts.disjoint.covers (past := []) (.arg reader) && checkTail facts rest
  | _, _, .store _ (.arg writer) _ rest =>
    if facts.same writer then true else facts.disjoint.covers (past := []) (.arg writer) && checkTail facts rest
  | _, _, _ => false

/-- Check a one-based Store version in the supplied entry table. -/
def cut (facts : AddressContract args) (version : Nat) (entry : Memory.Graph args) :
    Option (PrefixStore args × Memory.Graph args) :=
  if facts.consistent then
    Load.cutWith (fun store {_ _} tail => facts.disjoint.matches (past := []) (.arg store.address) && checkTail facts tail)
      version entry
  else none

/-- Optional earlier same-wire deletion. The existing checker with an
empty reader list admits this deletion uniformly at all valuations. -/
def cleanup (entry : Memory.Graph args) (prior : Option (Memory.DeadStore.Candidate × Port args .address)) :
    Memory.Graph args :=
  (prior.bind fun (candidate, port) => Memory.DeadStore.rewriteWith entry candidate ⟨port, []⟩).getD entry

structure Programs (cells : Nat) (args : List ValueSort) where
  overwriteDeleted : Bool
  original : Program cells args
  optimized : Program cells args

/-- Emit a fixed pair of MemRef CFGs. The version is relative to the table
after the optional cleanup. Refusal of the suffix check keeps that table. -/
def lower (cells : Nat) (graph : Graph args) (entry : Memory.Graph args)
    (version : Nat) (facts : AddressContract args)
    (prior : Option (Memory.DeadStore.Candidate × Port args .address) := none) : Programs cells args :=
  let current := cleanup entry prior
  let edit := cut facts version current
  ⟨edit.isSome, lowerDiamond cells graph (some entry),
    lowerDiamond cells graph (some ((edit.map Prod.snd).getD current))⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static
