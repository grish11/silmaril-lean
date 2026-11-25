module

import Silmaril.Languages.Python.Source.Closure.Thms
meta import Silmaril.Languages.Python.Source.Closure.Defs
meta import Silmaril.Languages.Python.Source.Scope.Defs
meta import Silmaril.Languages.Python.Source.Syntax.Defs

open Silmaril.Languages.Python.Source
open Silmaril.Languages.Python.Source.Closure

private def source : Module :=
  ⟨[.functionDef "outer" [{ name := "x" }, { name := "y" }] [
    .functionDef "middle" [] [
      .assign "z" (.integer 7),
      .functionDef "inner" [] [
        .return_ (some (.binary .add (.name "x") (.binary .add (.name "z") (.name "y"))))]]]]⟩

private def slots : Option (List (Capture × Bool × Nat) × List Nat) := do
  let tree ← (analyze source).toOption
  let middle ← tree.atPath [0, 0]
  let inner ← tree.atPath [0, 0, 0]
  let layout ← layout? middle inner.captures
  let positions := layout.entries.map fun entry =>
    match entry.slot with
    | .owned index _ _ => (entry.capture, true, index.val)
    | .forwarded index _ _ => (entry.capture, false, index.val)
  return (positions, layout.cells (fun index => 100 + index.val) (fun index => 200 + index.val))

#guard slots == some ([(⟨"x", [0]⟩, false, 0), (⟨"z", [0, 0]⟩, true, 0),
  (⟨"y", [0]⟩, false, 1)], [200, 100, 201])

#guard (match (analyze source).toOption with
  | none => false
  | some tree =>
    match tree.atPath [0], tree.atPath [0, 0, 0] with
    | some outer, some inner => (layout? outer inner.captures).isNone
    | _, _ => false)

#print axioms slot_iff
#print axioms layout_iff
#print axioms Layout.cells_length
