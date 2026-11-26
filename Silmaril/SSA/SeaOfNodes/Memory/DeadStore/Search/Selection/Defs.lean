module

public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Defs

/-! # Select one checked dead Store in native table order -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection

open RVSDG (Tuple)
open Memory.Forwarding.Disjoint (Certificate)

variable {args : List ValueSort} {cells : Nat}

/-- Enumerate the original one-based Store versions in table order. -/
def storeVersions : {past : List (List ValueSort)} → {version : Nat} →
    Body args past version → List Nat
  | _, _, .ret _ _ => []
  | _, _, .load _ _ rest => storeVersions rest
  | _, version, .store _ _ _ rest => (version + 1) :: storeVersions rest

structure Result (args : List ValueSort) where
  candidate : Candidate
  facts : Certificate args
  graph : Graph args

def tryStore (graph : Graph args) (input : Tuple (Val cells) args)
    (removeVersion : Nat) (facts : Certificate args) : Option (Result args) := do
  let candidate ← Search.discover graph removeVersion facts
  let rewritten ← Memory.DeadStore.rewrite graph candidate facts input
  some ⟨candidate, facts, rewritten⟩

/-- Select the first success by ascending Store version, then supplied
certificate order. For each attempt, the nominated search chooses the
first qualifying overwrite and the rewrite checks the concrete cells. -/
def rewrite (graph : Graph args) (certificates : List (Certificate args))
    (input : Tuple (Val cells) args) : Option (Result args) :=
  (storeVersions graph).findSome? fun version =>
    certificates.findSome? (tryStore graph input version)

end Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection
