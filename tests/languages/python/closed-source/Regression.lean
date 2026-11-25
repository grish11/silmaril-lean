module

import Silmaril.Languages.Python.Compile.Closed.Thms
meta import Silmaril.Languages.Python.Compile.Closed.Defs
meta import Silmaril.Languages.Python.Core.Thms
meta import Silmaril.Languages.Python.Source.Syntax.Defs

open Silmaril.Languages.Python
open Silmaril.Languages.Python.Compile.Closed

private def function (value : Source.Expr) : Source.Module :=
  ⟨[.functionDef "example" [] [.return_ (some value)]]⟩

private def sample : Source.Module :=
  function (.binary .add (.integer 1) (.integer 2))

example : Returns sample 3 := .function "example" (.add (.integer 1) (.integer 2))

#guard (match compile sample with
  | .error _ => false
  | .ok body =>
    match Core.run .addition body 3 with
    | some (.stop (.finished (.ok value)) (.observed (.returned (.ok observed)))) =>
      value == 3 && observed == 3
    | _ => false)

#guard (match compile (function (.call (.name "dynamic") [])) with
  | .error .expressionShape => true
  | _ => false)

#guard (match compile (function (.binary .floorDiv (.integer 1) (.integer 0))) with
  | .error .expressionShape => true
  | _ => false)

#guard (match compile ⟨[.nonlocalDecl ["unbound"]]⟩ with
  | .error (.scope ⟨[], .nonlocalInModule "unbound"⟩) => true
  | _ => false)

#guard (match compile ⟨[]⟩ with
  | .error .moduleShape => true
  | _ => false)

example (scopeAccepted : ∃ scope, Source.analyze ⟨[]⟩ = .ok scope) :
    compile ⟨[]⟩ = .error .moduleShape :=
  (rejects_iff _ _).mpr ⟨scopeAccepted, by rintro ⟨_, _, shape⟩; cases shape⟩

#print axioms compile_iff
#print axioms rejects_iff
#print axioms returns_exists
#print axioms initial
#print axioms observes_iff
#print axioms run_exact
