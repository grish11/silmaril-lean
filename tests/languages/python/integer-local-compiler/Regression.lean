module

import Silmaril.Languages.Python.Compile.Locals.Thms
meta import Silmaril.Languages.Python.Compile.Locals.Defs
meta import Silmaril.Languages.Python.Core.Locals.Thms
meta import Silmaril.Languages.Python.Source.Syntax.Defs

open Silmaril.Languages.Python
open Silmaril.Languages.Python.Compile.Locals

private def function (body : List Source.Stmt) : Source.Module :=
  ⟨[.functionDef "answer" [] body]⟩

private def sum : Source.Module :=
  function [.assignTargets [.name "x"] (.integer 41),
    .assign "y" (.binary .add (.name "x") (.integer 1)),
    .return_ (some (.name "y"))]

#guard (match compile sum with
  | .error _ => false
  | .ok compiled =>
    match Core.Locals.run compiled.code compiled.code.budget with
    | .stop (.finished store (.ok value)) (.observed (.returned (.ok observed))) =>
      value == 42 && observed == 42 &&
        (localNames compiled.scope) == ["x", "y"] &&
        (List.finRange (localNames compiled.scope).length |>.map store) == [some 41, some 42]
    | _ => false)

private def readBeforeAssign : Source.Module :=
  function [.assign "y" (.name "x"), .assign "x" (.integer 1), .return_ (some (.name "y"))]

#guard (match compile readBeforeAssign with
  | .error _ => false
  | .ok compiled =>
    match Core.Locals.run compiled.code compiled.code.budget with
    | .stop (.finished store (.error (.unboundLocal slot))) (.observed (.returned (.error _))) =>
      (localNames compiled.scope)[slot] == "x" &&
        (List.finRange (localNames compiled.scope).length |>.all fun i => (store i).isNone)
    | _ => false)

private def floorDivZero : Source.Module :=
  function [.assign "x" (.integer 7),
    .return_ (some (.binary .floorDiv (.name "x") (.integer 0)))]

#guard (match compile floorDivZero with
  | .error _ => false
  | .ok compiled =>
    match Core.Locals.run compiled.code compiled.code.budget with
    | .stop (.finished store (.error (.arithmetic .zeroDivisionError))) (.observed (.returned (.error _))) =>
      (List.finRange (localNames compiled.scope).length |>.map store) == [some 7]
    | _ => false)

#guard (match compile (function [.return_ (some (.name "outside"))]) with
  | .error (.unresolvedLocal "outside") => true
  | _ => false)

#print axioms Compiled.run_exact
#print axioms address_iff
