module

public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Defs

/-! # Discover the overwrite for one nominated dead Store -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search

open RVSDG (Tuple)
open Memory.Forwarding.Disjoint (Certificate)

variable {args : List ValueSort} {cells : Nat}

/-- Find the first later Store on the observed wire. A Load can be
passed only with the existing reader evidence. -/
def findOverwrite (facts : Certificate args) :
    {past : List (List ValueSort)} → {version : Nat} → Body args past version → Option Nat
  | _, _, .ret _ _ => none
  | _, _, .load _ address rest =>
    if !facts.matches address && facts.covers address then findOverwrite facts rest else none
  | _, version, .store _ address _ rest =>
    if facts.matches address then some (version + 1) else findOverwrite facts rest

def findAfter (removeVersion : Nat) (facts : Certificate args) :
    {past : List (List ValueSort)} → {version : Nat} → Body args past version → Option Nat
  | _, _, .ret _ _ => none
  | _, _, .load _ _ rest => findAfter removeVersion facts rest
  | _, version, .store _ address _ rest =>
    if version + 1 = removeVersion then
      if facts.matches address then findOverwrite facts rest else none
    else findAfter removeVersion facts rest

/-- Complete a nominated Store version using the supplied reader certificate.
The certificate's concrete inequalities remain obligations on the input. -/
def discover (graph : Graph args) (removeVersion : Nat) (facts : Certificate args) :
    Option Candidate :=
  (findAfter removeVersion facts graph).map (fun overwrite => ⟨removeVersion, overwrite⟩)

/-- Discover the overwrite and check the invocation before deleting. -/
def rewrite (graph : Graph args) (removeVersion : Nat) (facts : Certificate args)
    (input : Tuple (Val cells) args) : Option (Graph args) := do
  let candidate ← discover graph removeVersion facts
  Memory.DeadStore.rewrite graph candidate facts input

end Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search
