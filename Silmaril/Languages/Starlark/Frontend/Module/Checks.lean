module

meta import Lean.Elab.Tactic.Cbv
public import Silmaril.Languages.Starlark.Frontend.Module.Thms
import all Silmaril.Languages.Starlark.Frontend.Module.Defs
import all Silmaril.Languages.Starlark.Frontend.Defs
import all Silmaril.Languages.Starlark.Frontend.Lexer.Defs
import all Silmaril.Languages.Starlark.Modules.Resolve.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs
meta import Silmaril.Languages.Starlark.Modules.Defs
import all Silmaril.Languages.Starlark.Functions.Lowering.Resolve.Defs
import all Silmaril.Languages.Starlark.Functions.Denotation.Defs
import all Silmaril.Languages.Starlark.Functions.Expressions.Denotation.Defs
import all Silmaril.Languages.Starlark.Lists.Denotation.Defs

namespace Silmaril.Languages.Starlark.Frontend.Module

public inductive Observation where
  | exportedInt (value : Int)
  | undefinedName (name : String)
  | missingArgument (name : String)
  | multipleValues (name : String)
  | duplicateKey (key : String)
  | duplicateExplicitKeyword (name : String)
  | requiredAfterDefault (name : String)
  | uninitializedGlobal (name : String)
  | uninitializedLocal (name : String)
  | invalidStar | invalidStarStar
  deriving DecidableEq

public structure Control where
  name : String
  source : String
  expected : Observation

private def success := "# 雪\ndef id(x):\n  return x\nout = id(7)"
private def runtimeFailure := "# 雪\ndef id(x):\n  return x\nout = id()"
private def validationFailure := "def id(x):\n  return x\nout = id(missing)"
private def continuedCall :=
  "# choisit\r\ndef pick(flag, value):\r\n  if flag:\r\n    return value\r\n  else:\r\n    return 0\r\n" ++
  "_seed = 29\r\nout = pick(\r\n  False or True,\r\n  _seed if True else 1,\r\n)"

private def defaultPrefix := "# 雪\nseed = 7\ndef pick(seed=seed):\n  return seed\n"
private def defaultExport := defaultPrefix ++ "out = pick()"
private def namedOverride := defaultPrefix ++ "out = pick(seed=9)"
private def namedCollision := "def pick(x=1):\n  return x\nout = pick(2, x=3)"
private def defaultRunsEarly := "def pick(x=seed):\n  return x\nseed = 7\nout = pick(x=9)"
private def repeatedExplicit := "def pick(x=1):\n  return x\nout = pick(x=2, x=3)"
private def requiredAfterDefault := "def pick(x=1, y):\n  return y\nout = pick(y=2)"
private def spreadPrefix := "def pick(x, y, z=0):\n  return z if x and y else 0\n"
private def spreadExport := spreadPrefix ++ "out = pick(y=1, *[2], **{\"z\": 9})"
private def tupleExport := spreadPrefix ++ "out = pick(*(2, 1,), **{'z': 8})"
private def spreadCollision := "def pick(x=1):\n  return x\nout = pick(x=2, **{\"x\": 3})"
private def repeatedDisplayKey := "def pick(x=1):\n  return x\nout = pick(x=2, **{\"x\": 3, 'x': 4})"

/-- Acceptance and observation controls shared with the pinned Go tool. -/
public def controls : List Control := [
  ⟨"text-module-export", success, .exportedInt 7⟩,
  ⟨"text-module-continuation", continuedCall, .exportedInt 29⟩,
  ⟨"text-module-missing-argument", runtimeFailure, .missingArgument "x"⟩,
  ⟨"text-module-undefined-name", validationFailure, .undefinedName "missing"⟩,
  ⟨"defining-scope-default", defaultExport, .exportedInt 7⟩,
  ⟨"named-override", namedOverride, .exportedInt 9⟩,
  ⟨"positional-named-collision", namedCollision, .multipleValues "x"⟩,
  ⟨"default-runs-before-override", defaultRunsEarly, .uninitializedGlobal "seed"⟩,
  ⟨"duplicate-explicit-keyword", repeatedExplicit, .duplicateExplicitKeyword "x"⟩,
  ⟨"required-after-default", requiredAfterDefault, .requiredAfterDefault "y"⟩,
  ⟨"list-and-mapping-spread", spreadExport, .exportedInt 9⟩,
  ⟨"tuple-and-mapping-spread", tupleExport, .exportedInt 8⟩,
  ⟨"explicit-expanded-collision", spreadCollision, .multipleValues "x"⟩,
  ⟨"duplicate-key-in-display", repeatedDisplayKey, .duplicateKey "x"⟩]

private def observe (source : String) : Option Observation :=
  match runUtf8 source.toUTF8 with
  | .ok (.ok published _) =>
    match published.exports.lookup "out" with
    | some (.scalar (.int value)) => some (.exportedInt value)
    | _ => none
  | .ok (.error (.runtime (.missingArguments [name])) _) => some (.missingArgument name)
  | .ok (.error (.runtime .invalidStar) _) => some .invalidStar
  | .ok (.error (.runtime .invalidStarStar) _) => some .invalidStarStar
  | .ok (.error (.runtime (.multipleArgumentValues name)) _) => some (.multipleValues name)
  | .ok (.error (.runtime (.duplicateKey (.string key))) _) => some (.duplicateKey key)
  | .ok (.error (.runtime (.uninitialized ⟨.global, name⟩)) _) => some (.uninitializedGlobal name)
  | .ok (.error (.runtime (.uninitialized ⟨.local, name⟩)) _) => some (.uninitializedLocal name)
  | .error (.validation (.validation (.syntax (.duplicateExplicitKeyword name)))) =>
    some (.duplicateExplicitKeyword name)
  | .error (.validation (.validation (.syntax (.requiredAfterDefault name)))) =>
    some (.requiredAfterDefault name)
  | .error (.validation (.expression (.lexical (.undefinedName name)))) => some (.undefinedName name)
  | _ => none

section

set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

-- Use the resolver's equations during proof reduction to keep the executable
-- well-founded recursion from expanding inside the kernel.
private theorem readExpr_eq (context : Functions.Lowering.Resolve.Context)
    (expr : Functions.Lowering.Resolve.SourceExpr) :
    Modules.Resolve.readExpr context expr = monadLift
      ((Functions.Lowering.Resolve.resolveTracked context expr).mapError Modules.Resolve.Error.expression) := rfl

private theorem startsWith_eq_prefix (source pattern : String) :
    source.startsWith pattern = pattern.toList.isPrefixOf source.toList :=
  Bool.eq_iff_iff.mpr (String.startsWith_string_iff.trans List.isPrefixOf_iff_prefix.symm)

attribute [local cbv_eval] Modules.Resolve.compileBody.eq_def readExpr_eq startsWith_eq_prefix

-- Reduce through actual UTF-8 parsing, normalization, checked resolution, and publication.
example : observe success = some (.exportedInt 7) := by cbv
example : observe runtimeFailure = some (.missingArgument "x") := by cbv
example : observe validationFailure = some (.undefinedName "missing") := by cbv
example : observe defaultExport = some (.exportedInt 7) := by cbv
example : observe namedCollision = some (.multipleValues "x") := by cbv

end

#guard controls.all fun control => decide (observe control.source = some control.expected)

private def exportNames (source : String) : Option (List String) :=
  match runUtf8 source.toUTF8 with
  | .ok (.ok published _) => some (published.exports.map Prod.fst)
  | _ => none

#guard decide (exportNames continuedCall = some ["pick", "out"])

private def commandSpans (source : String) : Option (List Span) := do
  let parsed ← (parseUtf8 source.toUTF8).toOption
  return parsed.commands.map LocatedCommand.span

example : commandSpans success = some [⟨⟨6, 2, 1⟩, ⟨27, 3, 11⟩⟩, ⟨⟨28, 4, 1⟩, ⟨39, 4, 12⟩⟩] :=
  by decide +kernel

private def frontendDiagnostic (source : String) : Option Diagnostic :=
  match runUtf8 source.toUTF8 with
  | .error (.frontend diagnostic) => some diagnostic
  | _ => none

example : frontendDiagnostic "out = f(1 + 2)" =
    some ⟨.unsupported .operator, ⟨⟨8, 1, 9⟩, ⟨13, 1, 14⟩⟩⟩ := by decide +kernel

example : frontendDiagnostic "out = f(x=7, 8)" =
    some ⟨.callOrder .positionalAfterNamed, ⟨⟨13, 1, 14⟩, ⟨14, 1, 15⟩⟩⟩ := by decide +kernel

example : frontendDiagnostic "out = f(*[7], x=8)" =
    some ⟨.callOrder .argumentAfterStar, ⟨⟨14, 1, 15⟩, ⟨15, 1, 16⟩⟩⟩ := by decide +kernel

example : frontendDiagnostic "out = f(*xs().value)" =
    some ⟨.unsupported .attribute, ⟨⟨13, 1, 14⟩, ⟨14, 1, 15⟩⟩⟩ := by decide +kernel

example : frontendDiagnostic "out = f(1=7)" =
    some ⟨.expected "',' or ')'", ⟨⟨9, 1, 10⟩, ⟨10, 1, 11⟩⟩⟩ := by decide +kernel

example : frontendDiagnostic "out = f(,7)" =
    some ⟨.expected "an expression", ⟨⟨8, 1, 9⟩, ⟨9, 1, 10⟩⟩⟩ := by decide +kernel

private def parameterSpans : Option (List (String × Span × Option Span)) := do
  let commands ← (parseFile "def f(a, b=seed):\n  return a").toOption
  match commands with
  | [⟨_, .define fn⟩] =>
    some (fn.parameters.map fun parameter =>
      (parameter.name, parameter.span, parameter.defaultValue.map LocatedArgument.span))
  | _ => none

example : parameterSpans = some [("a", ⟨⟨6, 1, 7⟩, ⟨7, 1, 8⟩⟩, none),
    ("b", ⟨⟨9, 1, 10⟩, ⟨15, 1, 16⟩⟩, some ⟨⟨11, 1, 12⟩, ⟨15, 1, 16⟩⟩)] :=
  by decide +kernel

private def explicitNames : Option (List (String × Span)) := do
  let commands ← (parseFile "out = f(b=7, a=8, b=9)").toOption
  match commands with
  | [⟨_, .assignCall _ (.call _ _ arguments)⟩] =>
    some (arguments.named.map fun item => (item.name, item.nameSpan))
  | _ => none

example : explicitNames = some [("b", ⟨⟨8, 1, 9⟩, ⟨9, 1, 10⟩⟩),
    ("a", ⟨⟨13, 1, 14⟩, ⟨14, 1, 15⟩⟩), ("b", ⟨⟨18, 1, 19⟩, ⟨19, 1, 20⟩⟩)] := by decide +kernel

end Silmaril.Languages.Starlark.Frontend.Module
