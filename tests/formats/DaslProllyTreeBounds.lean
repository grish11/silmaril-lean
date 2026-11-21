module

import Silmaril.Semantics.Prolly.Bounds.Tree.Thms
import Silmaril.Semantics.Prolly.Frontier.Thms
meta import Silmaril.Semantics.Prolly.Bounds.Tree.Defs

open Silmaril.Semantics Silmaril.Semantics.Prolly
open scoped BigOperators

private def widthOnly : UniformBuckets Bool Nat := ⟨4, by decide, fun _ _ _ => false⟩

private theorem widthOnly_cap (keys : List Nat) : widthOnly.FrontierCap keys 0 1 := by
  intro level
  refine ⟨by decide, fun choices key _ => ?_⟩
  simp [widthOnly]

example (map : OrderedMap Nat Unit) :
    4 ^ 3 * (5 * (Finset.univ.filter fun sample : Bool => 3 < (build (widthOnly.policy sample) map).level).card) ≤
      2 ^ 3 * (Fintype.card Bool * map.entries.length) := by
  simpa [widthOnly] using uniform_build_depth_tail (map := map) (widthOnly_cap (map.entries.map Prod.fst)) 3

example (map : OrderedMap Nat Unit) :
    2 * (∑ sample : Bool, let tree := build (widthOnly.policy sample) map
                         (blockOccurrences (fun _ => ()) tree.level tree.root).length - 1) ≤
      2 * (Fintype.card Bool * map.entries.length) := by
  simpa [widthOnly] using uniform_build_occurrences (map := map) (widthOnly_cap (map.entries.map Prod.fst))
    (by decide) (fun _ _ => ())

public def main : IO Unit := do
  let keys := List.range 17
  let policy := widthOnly.policy false
  unless promotions policy keys.length 0 keys == [[3, 7, 11, 15, 16], [15, 16]] do
    throw (IO.userError "unexpected frontier sequence")
  unless (frontierAt policy 3 0 keys).isEmpty do
    throw (IO.userError "terminal frontier must not emit a further block")
  let some map := OrderedMap.ofEntries? (keys.map (·, ())) | throw (IO.userError "ordered fixture")
  let tree := build policy map
  unless tree.level == 2 && (blockOccurrences (fun _ => ()) tree.level tree.root).length == 8 do
    throw (IO.userError "depth or unfolded block count does not match frontier sequence")
