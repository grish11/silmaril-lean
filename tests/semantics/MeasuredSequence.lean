module

import Silmaril.Semantics.MeasuredSequence.Thms
meta import Silmaril.Semantics.MeasuredSequence.Defs

open Silmaril.Semantics.MeasuredSequence

private def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

public def main : IO Unit := do
  let left := ofList [10, 20]
  let middle : Tree Nat := .one 30
  let right := ofList [40, 50]
  let first := append (append left middle) right
  let second := append left (append middle right)
  let items := [10, 20, 30, 40, 50]
  check (decide (first ≠ second)) "raw history affects shape"
  check (decide (normalize first = normalize second)) "normalization removes that history"
  check (decide (splitAt second 2 = (left, append middle right))) "boundary split returns the original children"
  check (decide (set second 1 99 = .branch 5 (set left 1 99) (append middle right))) "set retains the other subtree"
  check (flatten (splice first 1 3 (ofList [71, 72])) == [10, 71, 72, 50]) "splice across joins"
  check (flatten (splice first 99 3 (.one 60)) == items ++ [60]) "splice clips beyond the end"
  check (size first == 5 && flatten first == items) "size is exact and original is unchanged"
  for index in List.range 8 do
    let parts := splitAt first index
    check (get? first index == items[index]?) "lookup, including missing index"
    check (flatten (set first index 77) == items.set index 77) "set, including missing index"
    check (flatten parts.1 == items.take index && flatten parts.2 == items.drop index) "clipped split"
  let corrupt : Tree Nat := .branch 99 .empty (.one 1)
  check (decide (normalize corrupt = .one 1)) "normalization rebuilds stale counts and collapses empties"
