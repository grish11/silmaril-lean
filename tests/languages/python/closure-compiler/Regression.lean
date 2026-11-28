module

import Silmaril.Languages.Python.Compile.Closure.Thms
meta import Silmaril.Languages.Python.Compile.Closure.Defs
meta import Silmaril.Languages.Python.Core.Closure.Defs
meta import Silmaril.Languages.Python.Source.Closure.Frame.Defs
meta import Silmaril.Languages.Python.Source.Closure.Defs
meta import Silmaril.Languages.Python.Source.Scope.Defs
meta import Silmaril.Languages.Python.Source.Syntax.Defs

open Silmaril.Languages.Python
open Silmaril.Languages.Python.Source
open Silmaril.Languages.Python.Compile.Closure

private def source : Module :=
  ⟨[.functionDef "outer" [{ name := "x" }, { name := "y" }] [
    .functionDef "middle" [] [
      .assign "z" (.integer 7),
      .functionDef "inner" [] [
        .return_ (some (.binary .add (.name "x") (.binary .add (.name "z") (.name "y"))))]]]]⟩

private def loweredParams : Option (List (Bool × Nat)) := do
  let tree ← (analyze source).toOption
  let outer ← tree.atPath [0]
  let checked ← Source.Closure.Frame.parameterLayout? outer
  return (parameters checked).slots.map fun slot => match slot with
    | .local index => (false, index.val)
    | .owned index => (true, index.val)

#guard loweredParams == some [(true, 0), (true, 1)]

private def closureResult : Option (List Nat × List Nat × Int) := do
  let tree ← (analyze source).toOption
  let parent ← tree.atPath [0, 0]
  let child ← tree.atPath [0, 0, 0]
  let captures ← Source.Closure.layout? parent child.captures
  let heap := Core.Closure.Heap.empty.reserve 100
  let (heap, frame) := Core.Closure.Frame.fresh (layout := frameLayout parent) heap
    (fun index => ⟨index.val + 1⟩)
  let closure := function 17 captures frame
  let fromOperands := frame.closure (codeRef child 17) (captureOperands captures)
  let (heap, childFrame) := closure.freshFrame heap
  let owned ← slot? parent "z"
  let captured ← slot? child "z"
  let (heap, _) ← (frame.write heap owned.val (.int 13)).toOption
  let result ← (childFrame.read heap captured.val).toOption
  match result with
  | .int value =>
    return (closure.captures.toList.map (·.address), fromOperands.captures.toList.map (·.address), value)
  | _ => none

#guard closureResult == some ([1, 100, 2], [1, 100, 2], 13)

#print axioms parameterSlot_injective
#print axioms parameters_order
#print axioms function_order
#print axioms capture_at
