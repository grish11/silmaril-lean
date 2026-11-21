module

import Batteries.Data.Except
import Silmaril.Semantics.Prolly.Operations.Thms
meta import Silmaril.Semantics.Prolly.Operations.Thms

open Silmaril.Semantics Silmaril.Semantics.Prolly
open OrderedMap (Overlap)

private def left : OrderedMap Nat String :=
  ⟨[(1, "one"), (3, "left three"), (5, "left five")], by decide⟩

private def right : OrderedMap Nat String :=
  ⟨[(2, "two"), (3, "right three"), (5, "right five"), (8, "eight")], by decide⟩

private def policy : Policy Nat := ⟨2, by decide, fun _ _ => false⟩

private def setLeft : OrderedSet Nat := ⟨[(1, ()), (3, ()), (8, ())], by decide⟩
private def setRight : OrderedSet Nat := ⟨[(3, ()), (4, ()), (8, ())], by decide⟩

private def inspect (result : Except Nat (OrderedMap Nat String)) : Except Nat (List (Nat × String)) :=
  result.map OrderedMap.entries

public def main : IO Unit := do
  unless inspect (left.combine .union Overlap.keepLeft right) ==
    .ok [(1, "one"), (2, "two"), (3, "left three"), (5, "left five"), (8, "eight")] do
    throw (IO.userError "left-biased union")
  unless inspect (left.combine .intersection Overlap.keepRight right) == .ok [(3, "right three"), (5, "right five")] do
    throw (IO.userError "right-biased intersection")
  unless inspect (left.combine .union Overlap.reject right) == .error 3 do
    throw (IO.userError "reject must fail on the least overlap, not key 5")
  let suffix : OrderedMap.Overlap Nat String Nat := fun _ leftValue rightValue => .ok (some (leftValue ++ rightValue))
  let merged := TypedMap.combine policy .intersection suffix (TypedMap.ofMap policy left) (TypedMap.ofMap policy right)
  match merged with
  | .error _ => throw (IO.userError "typed AST combine")
  | .ok result =>
    unless result.view.entries == [(3, "left threeright three"), (5, "left fiveright five")] do
      throw (IO.userError "typed AST recovery")
  let sameDomain : OrderedMap Nat String := ⟨[(1, "changed"), (3, "left three"), (5, "left five")], by decide⟩
  unless left.domainSubset sameDomain && !left.submap sameDomain && left.cardinality == 3 do
    throw (IO.userError "domain inclusion is not entry inclusion")
  let discard := Overlap.discard (Key := Nat) (Payload := Unit) (Error := Nat)
  unless (setLeft.combine .union discard setRight).map OrderedMap.keys == .ok [1, 4] do
    throw (IO.userError "symmetric difference")
  unless (setLeft.combine .intersection discard setRight).map OrderedMap.keys == .ok [] do
    throw (IO.userError "discarded intersection")
