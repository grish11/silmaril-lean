module

import Silmaril.Formats.PER.Parent.Thms
import Silmaril.Formats.PER.Partition.Operations.Thms
meta import Silmaril.Formats.PER.Parent.Thms
meta import Silmaril.Formats.PER.Partition.Operations.Thms

open Silmaril.Formats Silmaril.Formats.PER
open Silmaril.Semantics

private def terminalParents : Nat → Option Nat
  | 1 => some 2
  | 2 => some 3
  | 4 => some 5
  | _ => none

private theorem oneToThree : Parent.Reaches .terminalMissing terminalParents 1 3 :=
  .next ⟨rfl, by decide⟩ (.next ⟨rfl, by decide⟩ (.stop rfl))

example : (Parent.partition .terminalMissing terminalParents).rel 1 2 :=
  (Parent.rel_iff 1 2).mpr ⟨3, ⟨rfl, oneToThree⟩, ⟨rfl, .next ⟨rfl, by decide⟩ (.stop rfl)⟩⟩

example : ¬ (fibers terminalParents).rel 1 2 := by
  rintro ⟨label, left, right⟩
  exact (by decide : (2 : Nat) ≠ 3) (Option.some.inj (left.trans right.symm))

example : ¬ (Parent.partition .terminalMissing terminalParents).rel 1 4 := by
  intro related
  obtain ⟨root, left, right⟩ := (Parent.rel_iff 1 4).mp related
  have first := Parent.roots_functional left ⟨rfl, oneToThree⟩
  have second := Parent.roots_functional right ⟨rfl, .next ⟨rfl, by decide⟩ (.stop rfl)⟩
  exact (by decide : (3 : Nat) ≠ 5) (first.symm.trans second)

example : ¬ (Parent.partition .terminalMissing terminalParents).Dom 3 := by
  intro supported
  obtain ⟨_, known, _⟩ := (Parent.dom_iff 3).mp supported
  cases known

private def cycles : Nat → Option Nat
  | 0 => some 1
  | 1 => some 0
  | 2 => some 0
  | _ => none

example : (Parent.connectivity cycles).rel 1 2 :=
  (Parent.connectivity cycles).laws.trans (Parent.edge_connected (key := 1) (next := 0) rfl)
    ((Parent.connectivity cycles).laws.symm (Parent.edge_connected (key := 2) (next := 0) rfl))

private def labels (lookup : Nat → Option Nat) : Partition.FiniteMap Nat :=
  Partition.tabulate {1, 2, 3} lookup

private def first := labels (fun key => some (if key = 3 then 99 else 70))
private def second := labels (fun key => some (if key = 1 then 80 else 70))

example : fibers (Partition.intersectMaps first second).lookup? =
    Partition.meet (fibers first.lookup?) (fibers second.lookup?) :=
  Partition.intersectMaps_partition first second

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

public def main : IO Unit := do
  let common := Partition.intersectMaps first second
  check (([1, 2, 3] : List Nat).all fun key => common.lookup? key == some key) "meet splits all three keys"
  let filtered := Partition.restrictMap first {2, 3, 4}
  check (filtered.lookup? 2 == some 70 && filtered.lookup? 1 == none && filtered.lookup? 4 == none)
    "restriction preserves external labels and does not add new keys"
  let state := Partition.toUnionFind first
  let some merged := state.union 2 3 | throw (IO.userError "selected union failed")
  check (merged.sameClass 1 3 == some true && merged.sameClass 1 70 == none) "union retains support"
