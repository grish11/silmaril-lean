module

import Silmaril.Languages.Python.Source.Closure.Frame.Thms
meta import Silmaril.Languages.Python.Source.Closure.Frame.Defs
meta import Silmaril.Languages.Python.Source.Closure.Defs
meta import Silmaril.Languages.Python.Source.Scope.Defs
meta import Silmaril.Languages.Python.Source.Syntax.Defs

open Silmaril.Languages.Python.Source
open Silmaril.Languages.Python.Source.Closure
open Silmaril.Languages.Python.Source.Closure.Frame

private def source : Module :=
  ⟨[.functionDef "outer" [{ name := "x" }, { name := "y" }] [
    .assign "z" (.name "y"),
    .functionDef "inner" [] [.return_ (some (.name "x"))],
    .return_ (some (.name "z"))]]⟩

private def positions : Option (List Name × List (Bool × Nat) × List Capture) := do
  let tree ← (analyze source).toOption
  let parent ← tree.atPath [0]
  let child ← tree.atPath [0, 0]
  let parameters ← parameterLayout? parent
  let captures ← layout? parent child.captures
  let slots := parameters.destinations.toList.map fun destination =>
    match destination with
    | .inl index => (false, index.val)
    | .inr owned => (true, owned.val)
  return (ordinaryNames parent, slots, captures.entriesVector.toList.map Entry.capture)

#guard positions == some (["y", "z", "inner"], [(true, 0), (false, 0)], [⟨"x", [0]⟩])

#guard (match (analyze source).toOption.bind (·.atPath [0]) with
  | none => false
  | some scope =>
    let duplicated := { scope with context := { scope.context with parameters := ["x", "x"] } }
    (parameterLayout? duplicated).isNone)

#print axioms Layout.entriesVector_toList
#print axioms ParameterLayout.destinations_distinct
#print axioms ParameterLayout.destinations_names
