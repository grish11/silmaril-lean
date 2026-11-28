# SPDX-License-Identifier: MIT
"""Exercise the seeded runner on independently authored Python fixtures."""

import argparse
import ast
from contextlib import redirect_stderr, redirect_stdout
import hashlib
from io import StringIO
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile
from types import FunctionType
import warnings


IMPORTS = (
    "import Batteries.Data.Except",
    "import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Thms",
    "import Silmaril.Languages.Python.Core.Module.SeededCall.Observation.Thms",
    "meta import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs",
    "meta import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Defs",
    "meta import Silmaril.Languages.Python.Core.Module.Functions.Defs",
    "meta import Silmaril.Languages.Python.Core.Closure.Defs",
    "meta import Silmaril.Languages.Python.Core.Module.SeededCall.Defs",
    "meta import Silmaril.Languages.Python.Core.Module.SeededCall.Observation.Defs",
)

LEAN = """
open Silmaril.Languages.Python
open Core.Module.SeededCall

private def initial (profile : String) : Namespace :=
  let classes : Bindings := [("AssertionError", .exceptionClass .assertionError),
    ("TypeError", .exceptionClass .typeError), ("NameError", .exceptionClass .nameError)]
  let helpers (diagnostic : AssertionArgument) : Bindings :=
    [("require_error", .helper (.assertRaises diagnostic)), ("compare_ints", .helper .assertEqual)]
  match profile with
  | "builtin" => ⟨[], classes ++ helpers .empty⟩
  | "preamble" => ⟨helpers (.text "did not raise exception"), classes⟩
  | "legacy_builtin" => Compile.ModuleEntry.Functions.Run.Seeded.legacySeed .builtin
  | "legacy_preamble" => Compile.ModuleEntry.Functions.Run.Seeded.legacySeed .preamble
  | "legacy_bool_int_builtin" => Compile.ModuleEntry.Functions.Run.Seeded.legacyBoolIntSeed .builtin
  | "legacy_bool_int_preamble" => Compile.ModuleEntry.Functions.Run.Seeded.legacyBoolIntSeed .preamble
  | "legacy_bool_callable_builtin" => Compile.ModuleEntry.Functions.Run.Seeded.legacyBoolCallableSeed .builtin
  | "legacy_bool_callable_preamble" => Compile.ModuleEntry.Functions.Run.Seeded.legacyBoolCallableSeed .preamble
  | "legacy_bool_isinstance_builtin" => Compile.ModuleEntry.Functions.Run.Seeded.legacyBoolIsinstanceSeed .builtin
  | "legacy_bool_isinstance_preamble" => Compile.ModuleEntry.Functions.Run.Seeded.legacyBoolIsinstanceSeed .preamble
  | _ => .empty

private def detail : AssertionArgument → String
  | .empty => "empty"
  | .text text => "text:" ++ text
  | .integerPair left right => s!"pair:{left}:{right}"
  | .numericPair left right => s!"numeric-pair:{reprStr left}:{reprStr right}"
  | .boolean value => if value then "bool:True" else "bool:False"
  | .booleanPair left right => s!"bool-pair:{left}:{right}"
  | .textPair left right =>
    s!"text-pair:{reprStr (left.points.map UInt32.toNat)}:{reprStr (right.points.map UInt32.toNat)}"
  | .tuplePair left right => s!"tuple-pair:{reprStr left}:{reprStr right}"
  | .dictionaryPair left right => s!"dictionary-pair:{reprStr left}:{reprStr right}"
  | .emptyTuple => "tuple:()"
  | .listObject object => s!"list:{reprStr object.contents}"

private def raised : Raised → String
  | .assertionError argument => "AssertionError:" ++ detail argument
  | .runtime (.nameError name) => "NameError:" ++ name
  | .runtime .notCallable | .runtime .additionTypeError => "TypeError"
  | .runtime _ => "unexpected runtime error"

private def resultBinding : Option Value → String
  | none => "absent"
  | some .none => "None"
  | some (.int value) => s!"int:{value}"
  | some (.bool value) => if value then "bool:True" else "bool:False"
  | some (.function _) => "function"
  | _ => "unexpected binding"

private def inspect (source : Source.Module) (profile : String) : Option (List String) := do
  let compiled ← (Compile.ModuleEntry.Functions.Run.compile source).toOption
  let outcome := Compile.ModuleEntry.Functions.Run.Seeded.run (initial profile) compiled
  let completion := match outcome.completion with
    | .ok _ => "normal"
    | .error (.raised error) => raised error
    | .error .unsupported => "unsupported"
    | .error (.publicationFault _) => "publication fault"
    | .error (.varNamesFault _) => "varnames code fault"
    | .error (.callbackFault _) => "callback fault"
    | .error .callbackFuelExhausted => "callback fuel exhausted"
    | .error (.directCallFault _) => "direct call fault"
    | .error .directCallFuelExhausted => "direct call fuel exhausted"
  let catches := outcome.calls.filterMap (fun call => call.observation.caught.map raised)
  return completion :: (["result", "after"].map (resultBinding ∘ lookupBinding outcome.residual.moduleGlobals)) ++ catches

private def callNames (source : Source.Module) (profile : String) : Option (List String) := do
  let compiled ← (Compile.ModuleEntry.Functions.Run.compile source).toOption
  return (Compile.ModuleEntry.Functions.Run.Seeded.run (initial profile) compiled).calls.map (·.callee)

private def callValues (source : Source.Module) (profile : String) : Option (List (String × Value)) := do
  let compiled ← (Compile.ModuleEntry.Functions.Run.compile source).toOption
  let calls := (Compile.ModuleEntry.Functions.Run.Seeded.run (initial profile) compiled).calls
  calls.mapM fun call => do
    let value ← call.observation.result.toOption
    return (call.callee, value)

private def exactGlobals (source : Source.Module) (profile : String) (bindings : Bindings := []) : Bool :=
  match Compile.ModuleEntry.Functions.Run.compile source with
  | .error _ => false
  | .ok compiled =>
    let space := initial profile
    (Compile.ModuleEntry.Functions.Run.Seeded.run space compiled).residual.moduleGlobals ==
      bindings ++ space.moduleGlobals

private def adjacentKeywordEvidence (source : Source.Module) (profile : String) (value : Int) : Bool := Id.run do
  let .ok compiled := Compile.ModuleEntry.Functions.Run.compile source | return false
  let input := initial profile
  let outcome := Compile.ModuleEntry.Functions.Run.Seeded.run input compiled
  let some (.function function) := lookupBinding outcome.residual.moduleGlobals "probe" | return false
  let expected : Result := if value == 4 then .ok .none else .error (.raised (.assertionError .empty))
  let published := (input.bindGlobal "result" (.int 5)).bindGlobal "probe" (.function function)
  let residual := if value == 4 then published.bindGlobal "after" (.int 9) else published
  let [event] := outcome.calls | return false
  let some (some (.int retained)) := outcome.heap.lookup ⟨0⟩ | return false
  return event.callee == "probe" && event.observation.result == expected &&
    event.observation.caught.isNone && outcome.residual.builtins == input.builtins &&
    outcome.residual.moduleGlobals == residual.moduleGlobals &&
    outcome.heap.next == 1 && retained == value

private def ordinaryOutcome (source : Source.Module) (observed : String := "x") : Option (String × Option Int) := do
  let compiled ← (Compile.ModuleEntry.Functions.Run.compile source).toOption
  match (Compile.ModuleEntry.Functions.Run.runPrefix compiled.table 1000 compiled.start).2 with
  | .finished session completion =>
    let result := match completion with
      | .normal => "normal"
      | .raised (.nameError name) => "NameError:" ++ name
      | _ => "unexpected completion"
    match session.globals observed with
    | none => some (result, none)
    | some (.int value) => some (result, some value)
    | _ => none
  | _ => none

private def scalarEvidence (source : Source.Module) (profile completion : String)
    (bindings : Bindings) : Bool := Id.run do
  let .ok compiled := Compile.ModuleEntry.Functions.Run.compile source | return false
  let input := initial profile
  let heap : Core.Closure.Heap := ⟨1, fun address => if address == 0 then some (.int 23) else none⟩
  let seeded := Compile.ModuleEntry.Functions.Run.Seeded.run input compiled heap
  let (events, final) := Compile.ModuleEntry.Functions.Run.runPrefix compiled.table 1000
    (.ready (Compile.ModuleEntry.Functions.Run.seed .empty heap) compiled.instructions)
  let .finished session ordinary := final | return false
  let observed := match ordinary with
    | .normal => "normal"
    | .assertionError => "AssertionError:empty"
    | .raised (.nameError name) => "NameError:" ++ name
    | _ => "unexpected completion"
  let reached := (["result", "after"].map fun name => (session.globals name).map
    Compile.ModuleEntry.Functions.Run.Seeded.seededValue) ==
      (["result", "after"].map (lookupBinding bindings ·))
  let cell := some (.int 23 : Value)
  return observed == completion && reached && events.isEmpty && seeded.calls.isEmpty &&
    seeded.residual.moduleGlobals == bindings ++ input.moduleGlobals &&
    seeded.residual.builtins == input.builtins && session.heap.next == 1 && seeded.heap.next == 1 &&
    (session.heap.contents 0).map Compile.ModuleEntry.Functions.Run.Seeded.seededValue == cell &&
    (seeded.heap.contents 0).map Compile.ModuleEntry.Functions.Run.Seeded.seededValue == cell

private def trueAssertionOperands (source : Source.Module) (profile : String) (count : Nat) : Bool :=
  match Compile.ModuleEntry.Functions.Run.compile source with
  | .error _ => false
  | .ok compiled =>
    compiled.instructions.length == count && compiled.instructions.all fun instruction =>
      match instruction with
      | .scalar (.assertion test) =>
        match Compile.ModuleEntry.Functions.Run.evaluate (Compile.ModuleEntry.Functions.Run.seed .empty) test,
            Compile.ModuleEntry.Functions.Run.Seeded.evaluateScalar (initial profile) false test with
        | .ok (.bool true), .ok (.bool true) => true
        | _, _ => false
      | _ => false

private def additionEvidence (source : Source.Module) (profile : String) (succeeds : Bool) : Bool := Id.run do
  let .ok compiled := Compile.ModuleEntry.Functions.Run.compile source | return false
  let space := initial profile
  let run := Compile.ModuleEntry.Functions.Run.Seeded.run space compiled
  let some (.function fn) := run.residual.lookupGlobal "probe" | return false
  let [call] := run.calls | return false
  let some (.int cell) := run.heap.contents 0 | return false
  let space := if succeeds then space.bindGlobal "increment" (.int 1) else space
  let expected := (space.bindGlobal "probe" (.function fn)).bindGlobal "result" (.int 5)
  let expected := if succeeds then expected.bindGlobal "after" (.int 9) else expected
  let expectedResult := if succeeds then .ok (.int 6) else .error (.raised (.runtime .additionTypeError))
  return run.residual.moduleGlobals == expected.moduleGlobals && run.residual.builtins == expected.builtins &&
    run.heap.next == 1 && cell == 5 &&
    call.callee == "probe" && call.observation.result == expectedResult && call.observation.caught.isNone

private def equalityBeforeAssertNot (source : Source.Module) : Bool :=
  match Compile.ModuleEntry.Functions.Run.compile source with
  | .ok compiled =>
    match compiled.instructions with
    | [.scalar (.assertion (.binary .equal ..)), .assertNot (.binary .equal ..)] => true
    | _ => false
  | .error _ => false

private def singleNoneReturn (source : Source.Module) (profile : String) : Bool :=
  match Compile.ModuleEntry.Functions.Run.compile source with
  | .error _ => false
  | .ok compiled =>
    match (Compile.ModuleEntry.Functions.Run.Seeded.run (initial profile) compiled).calls with
    | [call] => match call.observation.result with
      | .ok .none => true
      | _ => false
    | _ => false

private def publicationReceipt (source : Source.Module) (profile : String) : Option String := do
  let compiled ← (Compile.ModuleEntry.Functions.Run.compile source).toOption
  let [.publish name top, .call .discard callee operands] := compiled.instructions | none
  let space := initial profile
  let expectedSpace := space.bindGlobal name (.function top.closure)
  let result := Compile.ModuleEntry.Functions.Run.Seeded.run space compiled
  if result.residual.moduleGlobals != expectedSpace.moduleGlobals || result.residual.builtins != expectedSpace.builtins
    then none else
  let [event] := result.calls | none
  if event.callee != callee then none else
  let resolved := resolveCall result.residual #v[] (.global callee)
    (operands.map Compile.ModuleEntry.Functions.Run.Seeded.lowerCallOperand)
  match resolved, event.observation.result, event.observation.caught with
  | .error (.raised (.runtime (.nameError missing))), .error (.raised (.runtime (.nameError observed))), none =>
    if missing == callee && observed == missing then some "callee lookup" else none
  | .ok (function, arguments), .ok .none, some (.assertionError .empty) =>
    match Request.decode function arguments with
    | .expect expectation (.function callback) [] _ =>
      if expectation.expected == .assertionError && callback == top.closure
        then some "caught callback assertion" else none
    | _ => none
  | _, _, _ => none

private def directDiscardReceipt (source : Source.Module) (profile : String) : Option (Nat × Int) := do
  let compiled ← (Compile.ModuleEntry.Functions.Run.compile source).toOption
  let [.publish name top, .call .discard callee []] := compiled.instructions | none
  let space := initial profile
  let expected := space.bindGlobal name (.function top.closure)
  let outcome := Compile.ModuleEntry.Functions.Run.Seeded.run space compiled
  let .ok () := outcome.completion | none
  let [event] := outcome.calls | none
  let .ok .none := event.observation.result | none
  let none := event.observation.caught | none
  if callee != name || event.callee != name || outcome.residual.moduleGlobals != expected.moduleGlobals ||
      outcome.residual.builtins != expected.builtins then none else
  let some (some (.int value)) := outcome.heap.lookup ⟨0⟩ | none
  return (outcome.heap.next, value)
"""

AUDIT = """
#print axioms Compile.ModuleEntry.Functions.Run.Seeded.run_preserves_builtins
#print axioms Compile.ModuleEntry.Functions.Run.Seeded.failing_instruction
#print axioms Compile.ModuleEntry.Functions.Run.Seeded.assertNot_operand_failure
#print axioms Compile.ModuleEntry.Functions.Run.Seeded.observeArguments_iff
#print axioms Compile.ModuleEntry.Functions.Run.Seeded.observeNestedCall_failedArguments
#print axioms Compile.ModuleEntry.Functions.Run.Seeded.callback_path
#print axioms Compile.ModuleEntry.Functions.Run.Seeded.callback_delivers
#print axioms Compile.ModuleEntry.Functions.Run.Seeded.callback_seedOnlyGlobal
#print axioms Compile.ModuleEntry.Functions.Run.Seeded.run_directDiscard
#print axioms Compile.ModuleEntry.Functions.Run.Seeded.run_directDiscard_unsupported
#print axioms runObserved_result
#print axioms Expectation.caught_iff
"""

UPSTREAM_REVISION = "b7ff99372dd24845cf84e58c96b877f15764b276"
BOOL_INT_PROFILES = ("legacy_bool_int_builtin", "legacy_bool_int_preamble")
BOOL_CALLABLE_PROFILES = ("legacy_bool_callable_builtin", "legacy_bool_callable_preamble")
BOOL_ISINSTANCE_PROFILES = ("legacy_bool_isinstance_builtin", "legacy_bool_isinstance_preamble")
OPT_IN_PROFILES = (*BOOL_INT_PROFILES, *BOOL_CALLABLE_PROFILES, *BOOL_ISINSTANCE_PROFILES)
UPSTREAM_CASE = "tests/python/programs/original/lambda-py/python-reference/exceptions/assertion-error.py"
UPSTREAM_SHA256 = "822abc163f457af8784c41c08cef152ecbb1266bb9704197292944386bc3dd79"
UPSTREAM_BOOL_DIR = "tests/python/programs/original/lambda-py/python-reference/bool"
UPSTREAM_ASSERT_NOT_CASE = "tests/python/programs/original/k-python/programs/testintegers1.py"
UPSTREAM_ASSERT_NOT_SHA256 = "295e494847f164f28f922f9eeb34a7344a199f51bb759eb043f88f06a1a31d61"
UPSTREAM_ASSIGN_CASE = "tests/python/programs/original/k-python/programs/testassign1.py"
UPSTREAM_ASSIGN_SHA256 = "7fc33245631f77c0dcfd63277f906b580c6034c487b189cc1f32dc4872efed63"
UPSTREAM_PUBLICATION_CASE = "tests/python/programs/original/lambda-py/python-reference/exceptions/assert-silent.py"
UPSTREAM_PUBLICATION_SHA256 = "c4664c5343be15e123a772fb1d7f49819b3ba9781266c6900172d653bdd26ada"
UPSTREAM_DIRECT_DISCARD_CASE = "tests/python/programs/original/k-python/programs/testscope3.py"
UPSTREAM_DIRECT_DISCARD_SHA256 = "8cd010d3911293c1dfe2da09adf3b40c8fcb258ecd85dd9847e65d5555866924"
UPSTREAM_LITERAL_IF_CASE = "tests/python/programs/original/k-python/programs/testintegers5.py"
UPSTREAM_LITERAL_IF_SHA256 = "a65342d9d5bc36848971fe5628ee00379edacee5a20cc406c790f4ef128222b8"
UPSTREAM_CONDITIONAL_EXPR_CASE = "tests/python/programs/original/k-python/programs/testif.py"
UPSTREAM_CONDITIONAL_EXPR_SHA256 = "3e35304b328295b30ffa6dbba0b50d7b6e1b10872e4138616a9bc3cd87d5ee4f"
UPSTREAM_CLOSED_SEQUENCE_CASE = "tests/python/programs/original/k-python/programs/testlists7.py"
UPSTREAM_CLOSED_SEQUENCE_SHA256 = "d50543ac9fafb3800a8ff5027d4decd65c6cfb9b94939fb1602e37f71bdb4492"
UPSTREAM_LITERAL_TUPLE_COMPARISONS = (
    ("tests/python/programs/original/k-python/programs/testin.py",
     "00a7ea2904c8b31edf06a507d337cbb21b416b4371cb4afe6dde8697f55dc8ac"),
    ("tests/python/programs/original/k-python/programs/testtuples1.py",
     "e6835512c2b669200b60a1e0fece8985616c744d80ce044c21bdd7678befc89a"),
)
UPSTREAM_LITERAL_COMPARISON_CHAINS = (
    ("tests/python/programs/original/k-python/programs/testbools9.py",
     "6394764cbf11f20dba5c6d67620aeb99c35f7fec12c174c4ec4be8f53d7719cf"),
    ("tests/python/programs/original/k-python/programs/testintegers4.py",
     "afb92835ef43e62344db39336dce513243bb89d31021c839cfd4519772b1ddb2"),
)
UPSTREAM_LITERAL_TRUTH = (
    ("tests/python/programs/original/k-python/programs/testbools3.py",
     "f1c6cf0c91765eb1244c876fa19649c0ae53c257c12fb16c7ff9f4ac8e5a9dba"),
    ("tests/python/programs/original/k-python/programs/testbools4.py",
     "456ec02381e7ba09f3b8a9ebd330d537b39d114cb405608c64a2343f143249d5"),
)
UPSTREAM_SINGLETON_IDENTITY_CASE = "tests/python/programs/original/k-python/programs/testis.py"
UPSTREAM_SINGLETON_IDENTITY_SHA256 = "f02f9072633592a48e89434d4ff3e59d6e633c47f93ff63dc23cb70ce7595bb7"
UPSTREAM_DEAD_BOOLEAN_CASE = "tests/python/programs/original/k-python/programs/testbools1.py"
UPSTREAM_DEAD_BOOLEAN_SHA256 = "4460b8a8f68da90dd09b0d491019c82def8b75d29d9edc71292cd7300b704c69"
UPSTREAM_NONE_VALUE_CASE = "tests/python/programs/original/lambda-py/python-reference/types/address-of-none.py"
UPSTREAM_NONE_VALUE_SHA256 = "6915793674cc89745a2cc378a00b71f42051087d0fe3d8fdf3787900031d9ca4"
UPSTREAM_SCALAR_WARNINGS = {
    UPSTREAM_LITERAL_TRUTH[0][0]: (
        ("SyntaxWarning", 2, "assertion is always true, perhaps remove parentheses?"),
    ),
}
UPSTREAM_LITERAL_INDEXING = (
    ("tests/python/programs/original/k-python/programs/testlists2.py",
     "7f4fdac9762c64a4355649bab7aeba840c94512eb11831621d60660ce7aa644e"),
    ("tests/python/programs/original/k-python/programs/testtuples9.py",
     "0147158c9fa7523038e49436eec9649707edd8023411f1ccef367f3ddb3306a3"),
)
UPSTREAM_NO_OP = (
    ("tests/python/programs/original/k-python/programs/testpass.py",
     "9f56e761d79bfdb34304a012586cb04d16b435ef6130091a97702e559260a2f2"),
    ("tests/python/programs/original/lambda-py/modules/test_as/empty.py",
     "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
    ("tests/python/programs/original/lambda-py/modules/test_as/__init__.py",
     "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
)
UPSTREAM_NESTED = (
    ("bool-callable.py", "8ec834148893367fc4ffe9a5645ea4a954293eb20a8188552e46b6dea4df4766",
     "___assertIs", "___assertIs", []),
    ("bool-int.py", "2b1b6ffc7d454e1cbe5820831c91ef40bcfbf962ad0e6845aab23dc7d290183d",
     "___assertEqual", "int", ["int"]),
    ("bool-isinstance.py", "86650e65b81e1523ee2ac6b29ff98f752c7e0077406534a4aa97f63daa254053",
     "___assertIs", "___assertIs", []),
)

SUCCESS = """result = require_error(AssertionError, compare_ints, -4, 7)
after = 9
"""

# An expected vector contains the terminal observation, two selected module
# bindings, then the assertion caught by each outer expectation.
ADJACENT_KEYWORD = """result = 5
def probe(value):
    def read():
        return value
    read()
    assert value == 4
probe(**{"value": %d})
after = 9
"""

ADDITION = """def probe():
    def read():
        return result
    result = 4
    result = result + 1
    saved = read()
    return saved + %s
result = 5
probe()
after = 9
"""

FIXTURES = (
    ("empty", "empty", "result = 5\n" + SUCCESS, ["NameError:require_error", "int:5", "absent"]),
    ("builtin", "builtin", SUCCESS, ["normal", "None", "int:9", "AssertionError:pair:-4:7"]),
    ("preamble", "preamble", SUCCESS, ["normal", "None", "int:9", "AssertionError:pair:-4:7"]),
    ("shadow", "builtin", "require_error = 42\nresult = 5\n" + SUCCESS, ["TypeError", "int:5", "absent"]),
    ("wrong_class", "builtin", SUCCESS.replace("AssertionError", "TypeError"),
     ["AssertionError:pair:-4:7", "absent", "absent"]),
    ("uncaught", "builtin", "result = 5\ncompare_ints(6, 8)\nafter = 9\n",
     ["AssertionError:pair:6:8", "int:5", "absent"]),
    ("no_error_basis", "builtin", SUCCESS.replace("-4, 7", "7, 7"),
     ["AssertionError:empty", "absent", "absent"]),
    ("no_error_preamble", "preamble", SUCCESS.replace("-4, 7", "7, 7"),
     ["AssertionError:text:did not raise exception", "absent", "absent"]),
    ("unsupported", "builtin", "require_error(AssertionError, AssertionError)\n",
     ["unsupported", "absent", "absent"]),
    ("nested_missing_outer", "empty", "result = 5\nouter(inner(1))\nafter = 9\n",
     ["NameError:outer", "int:5", "absent"]),
    ("nested_returns", "builtin", """result = require_error(
    TypeError, require_error(AssertionError, compare_ints, 1, 2), compare_ints(3, 3))
after = 9
""", ["normal", "None", "int:9", "AssertionError:pair:1:2", "TypeError"]),
    ("nested_first_failure", "builtin", """outer = 42
result = 5
result = outer(compare_ints(4, 5), later_missing(1))
after = 9
""", ["AssertionError:pair:4:5", "int:5", "absent"]),
    ("nested_missing_argument", "builtin", """result = 5
result = require_error(TypeError, compare_ints(1, 1), missing, later_missing(1))
after = 9
""", ["NameError:missing", "int:5", "absent"]),
    ("nested_assertion", "preamble", """result = 5
assert require_error(TypeError, compare_ints(1, 1))
after = 9
""", ["AssertionError:empty", "int:5", "absent", "TypeError"]),
    ("nested_unsupported", "builtin", """result = 5
result = require_error(AssertionError, AssertionError())
after = 9
""", ["unsupported", "int:5", "absent"]),
    ("assert_not_zero", "empty", "result = 0\nassert not 0\nassert not result\nafter = 9\n",
     ["normal", "int:0", "int:9"]),
    ("assert_not_none", "builtin", """result = require_error(AssertionError, compare_ints, 1, 2)
assert not result
after = 9
""", ["normal", "None", "int:9", "AssertionError:pair:1:2"]),
    ("assert_not_truthy", "empty", "result = 5\nassert not -2\nafter = 9\n",
     ["AssertionError:empty", "int:5", "absent"]),
    ("assert_not_missing", "empty", "result = 5\nassert not missing\nafter = 9\n",
     ["NameError:missing", "int:5", "absent"]),
    ("assert_not_shadow", "builtin", "compare_ints = 0\nassert not compare_ints\nafter = 9\n",
     ["normal", "absent", "int:9"]),
    ("equality_true", "empty", """result = True == 1
assert result
assert (result == True) == 1
after = 9
""", ["normal", "bool:True", "int:9"]),
    ("equality_false", "empty", "result = False == -1\nassert not result\nafter = 9\n",
     ["normal", "bool:False", "int:9"]),
    ("equality_failed_assertion", "empty", "result = 5\nassert 1 == -1\nafter = 9\n",
     ["AssertionError:empty", "int:5", "absent"]),
    ("equality_missing_left", "empty", "result = 5\nresult = missing_left == missing_right\nafter = 9\n",
     ["NameError:missing_left", "int:5", "absent"]),
    ("equality_missing_right", "builtin", "result = 5\nresult = compare_ints == missing_right\nafter = 9\n",
     ["NameError:missing_right", "int:5", "absent"]),
    ("equality_unsupported_domain", "builtin", "result = 5\nresult = compare_ints == 1\nafter = 9\n",
     ["unsupported", "int:5", "absent"]),
    ("equality_unsupported_arithmetic", "empty", "result = 5\nassert not (1 + 2 == 4)\nafter = 9\n",
     ["unsupported", "int:5", "absent"]),
    ("standalone_boolean_unsupported", "empty", "result = 5\nassert not False\nafter = 9\n",
     ["unsupported", "int:5", "absent"]),
    ("publish_shadow", "builtin", """def compare_ints():
    assert 0
result = compare_ints
assert result
after = 9
""", ["normal", "function", "int:9"]),
    ("callback_live_binding", "builtin", """flag = 1
def callback():
    assert flag
flag = 0
result = require_error(AssertionError, callback)
after = 9
""", ["normal", "None", "int:9", "AssertionError:empty"]),
    ("callback_mismatch", "builtin", """result = 5
def callback():
    assert 0
result = require_error(TypeError, callback)
after = 9
""", ["AssertionError:empty", "int:5", "absent"]),
    ("callback_returns_builtin", "builtin", """def callback():
    return 42
require_error(AssertionError, callback)
after = 9
""", ["AssertionError:empty", "absent", "absent"]),
    ("callback_returns_preamble", "preamble", """def callback():
    pass
require_error(AssertionError, callback)
after = 9
""", ["AssertionError:text:did not raise exception", "absent", "absent"]),
    ("callback_missing_name", "preamble", """def callback():
    assert absent_name
result = require_error(NameError, callback)
after = 9
""", ["normal", "None", "int:9", "NameError:absent_name"]),
    ("callback_earlier_error", "preamble", """def callback():
    assert 0
    assert require_error
result = require_error(AssertionError, callback)
""", ["normal", "None", "absent", "AssertionError:empty"]),
    ("callback_seed_only_read", "builtin", """def callback():
    assert require_error
require_error(NameError, callback)
after = 9
""", ["unsupported", "absent", "absent"]),
    ("callback_positional_unsupported", "builtin", """def callback(parameter):
    assert parameter
require_error(AssertionError, callback, 0)
""", ["unsupported", "absent", "absent"]),
    ("callback_parameter_unsupported", "builtin", """def callback(parameter):
    assert parameter
require_error(TypeError, callback)
""", ["unsupported", "absent", "absent"]),
    ("direct_defined_assertion", "builtin", """def callback():
    assert 0
callback()
after = 9
""", ["AssertionError:empty", "absent", "absent"]),
    ("direct_live_shadow", "builtin", """def f():
    assert 0
f = 7
result = 5
f()
after = 9
""", ["TypeError", "int:5", "absent"]),
    ("direct_bind_unsupported", "empty", "def f():\n    return 1\nresult = 5\nresult = f()\nafter = 9\n",
     ["unsupported", "int:5", "absent"]),
    ("direct_assert_unsupported", "empty", "def f():\n    return 1\nassert f()\nafter = 9\n",
     ["unsupported", "absent", "absent"]),
    ("direct_positional_unsupported", "empty", "def f(value):\n    assert value\nf(1)\nafter = 9\n",
     ["unsupported", "absent", "absent"]),
    ("direct_nested_published", "builtin", "def f():\n    return 1\ncompare_ints(f(), 1)\nafter = 9\n",
     ["normal", "absent", "int:9"]),
    ("direct_nested_positional_unsupported", "builtin",
     "def f(value):\n    return value\ncompare_ints(f(1), 1)\nafter = 9\n",
     ["unsupported", "absent", "absent"]),
    ("literal_if_order", "legacy_builtin", """result = 5
if -1:
    result = 7
    kept = result
    assert True
else:
    assert missing
if 0:
    assert False
else:
    after = kept
""", ["normal", "int:7", "int:7"]),
    ("literal_if_failure", "legacy_preamble", """result = 5
if False:
    assert missing
else:
    result = 7
    assert False
    result = 8
after = 9
""", ["AssertionError:empty", "int:7", "absent"]),
    ("literal_if_missing", "empty", """result = 5
if True:
    result = 7
    assert missing
    assert False
else:
    result = 8
after = 9
""", ["NameError:missing", "int:7", "absent"]),
    ("literal_conditional_true", "legacy_bool_callable_builtin", """result = True if -1 else missing
___assertIs(result, True)
after = 1 // 0 if 0 else 1
""", ["normal", "bool:True", "int:1"]),
    ("literal_conditional_false", "empty", """result = 1 if 0 else False
assert not result
after = 5
""", ["normal", "bool:False", "int:5"]),
    ("literal_conditional_missing", "legacy_preamble", """result = 7
result = skipped if False else selected_missing
after = 9
""", ["NameError:selected_missing", "int:7", "absent"]),
    ("literal_conditional_assertion", "empty", """result = 7
assert False if True else missing
after = 9
""", ["AssertionError:empty", "int:7", "absent"]),
    ("literal_conditional_unsupported", "empty", """result = 7
result = skipped if False else 1 // 0
after = 9
""", ["unsupported", "int:7", "absent"]),
    ("closed_sequence_typed", "legacy_builtin", """result = [] + [True] + [-2, False] == [1, -2, 0]
after = (True,) + (False,) != (1, 0)
assert [1, 2] != (1, 2)
assert [1] != [1, 1]
""", ["normal", "bool:True", "bool:False"]),
    ("closed_sequence_failed_assertion", "empty", """result = 7
assert ([1, 2] + [3]) == [1, 3, 2]
after = 9
""", ["AssertionError:empty", "int:7", "absent"]),
    ("closed_sequence_enclosing_lookup", "legacy_preamble", """result = 7
result = (([1] + [2]) == [1, 2]) == missing
after = 9
""", ["NameError:missing", "int:7", "absent"]),
    ("literal_tuple_typed_bindings", "legacy_bool_callable_builtin", """result = (True, -2) == (1, -2)
after = False not in (0,)
___assertIs(result, True)
___assertIs(after, False)
""", ["normal", "bool:True", "bool:False"]),
    ("literal_tuple_failed_assertion", "empty", """result = 7
assert (1, 2) == (1,)
after = 9
""", ["AssertionError:empty", "int:7", "absent"]),
    ("literal_tuple_operand_failure_order", "legacy_preamble", """result = 7
result = (1 in (True,)) == (missing == later)
after = 9
""", ["NameError:missing", "int:7", "absent"]),
    ("literal_chain_typed_bindings", "legacy_bool_callable_builtin", """result = -1 < False <= True == 1
after = 0 < 2 > 3
assert 0 < 2 > 1
___assertIs(result, True)
___assertIs(after, False)
""", ["normal", "bool:True", "bool:False"]),
    ("literal_chain_failed_assertion", "empty", """result = 7
assert 1 < 0 < -1
after = 9
""", ["AssertionError:empty", "int:7", "absent"]),
    ("literal_chain_failure_order", "legacy_preamble", """result = 7
result = (0 < 2 > 1) == (missing == later)
after = 9
""", ["NameError:missing", "int:7", "absent"]),
    ("literal_truth_selected_types", "legacy_bool_callable_builtin", """result = 0 or True
after = True and -2 and 9
___assertIs(result, True)
assert [False]
assert not None
""", ["normal", "bool:True", "int:9"]),
    ("literal_truth_falsy_selected", "empty", """result = False and 7
after = 5 or False
assert not ()
""", ["normal", "bool:False", "int:5"]),
    ("literal_truth_failed_assertion", "empty", """result = 7
assert []
after = 9
""", ["AssertionError:empty", "int:7", "absent"]),
    ("literal_truth_failure_order", "legacy_preamble", """result = 7
result = (0 or -2) == (missing == later)
after = 9
""", ["NameError:missing", "int:7", "absent"]),
    ("none_value_tags", "empty", """result = None
alias = result
assert alias == None
assert result != False
assert not result
after = result != 0
assert not (False != 0)
""", ["normal", "None", "bool:True"]),
    ("none_value_left_lookup", "legacy_builtin", """result = None
result = missing_first != missing_second
after = 9
""", ["NameError:missing_first", "None", "absent"]),
    ("none_value_right_lookup", "legacy_preamble", """result = None
result = result != missing_right
after = 9
""", ["NameError:missing_right", "None", "absent"]),
    ("none_value_arithmetic_profile", "empty", """result = None
result = result + 1
after = 9
""", ["unsupported", "None", "absent"]),
    ("none_value_failed_assertion", "empty", """result = None
assert result != None
after = 9
""", ["AssertionError:empty", "None", "absent"]),
    ("singleton_identity_tags", "empty", """result = None is False
after = False is not True is (1 == True)
assert None is None
assert None is not False
assert not (False is True)
assert False == 0
""", ["normal", "bool:False", "bool:True"]),
    ("singleton_identity_skipped", "legacy_builtin", """result = False is True is (missing_tail == 0)
after = None
""", ["normal", "bool:False", "None"]),
    ("singleton_identity_left_lookup", "legacy_preamble", """result = None
result = (missing_left == 0) is (missing_middle == 0) is (missing_tail == 0)
after = 9
""", ["NameError:missing_left", "None", "absent"]),
    ("singleton_identity_middle_lookup", "legacy_builtin", """result = None
result = False is (missing_middle == 0) is (missing_tail == 0)
after = 9
""", ["NameError:missing_middle", "None", "absent"]),
    ("singleton_identity_tail_lookup", "legacy_preamble", """result = None
result = False is not True is (missing_tail != 0)
after = 9
""", ["NameError:missing_tail", "None", "absent"]),
    ("singleton_identity_failed_assertion", "empty", """result = None
assert False is None
after = 9
""", ["AssertionError:empty", "None", "absent"]),
    ("dead_boolean_suffix", "legacy_builtin", """result = True and False and (5 / 0) and (1 // 0)
after = False or True or (5 / 0)
assert (False and (True and 5 / 0)) is False
""", ["normal", "bool:False", "bool:True"]),
    ("dead_boolean_integer_tags", "legacy_preamble", """result = 0 and (5 / 0)
after = 7 or (5 / 0)
""", ["normal", "int:0", "int:7"]),
    ("bool_int_false", "legacy_bool_int_builtin", """result = int(False)
___assertEqual(result, 0)
___assertIsNot(result, False)
after = 9
""", ["normal", "int:0", "int:9"]),
    ("bool_int_true", "legacy_bool_int_preamble", """result = int(True)
___assertEqual(result, 1)
___assertIsNot(True, result)
after = 9
""", ["normal", "int:1", "int:9"]),
    ("bool_int_shadow", "legacy_bool_int_builtin", """result = 5
int = 7
result = int(False)
after = 9
""", ["TypeError", "int:5", "absent"]),
    ("bool_int_argument_order", "legacy_bool_int_preamble", """result = 5
___assertIsNot(int(True), missing)
after = 9
""", ["NameError:missing", "int:5", "absent"]),
    ("bool_int_defined_assertion", "legacy_bool_int_builtin", """result = 5
___assertEqual(int(True), 0)
after = 9
""", ["AssertionError:pair:1:0", "int:5", "absent"]),
    ("bool_int_other_conversion", "legacy_bool_int_builtin", "result = 5\nresult = int(1)\nafter = 9\n",
     ["unsupported", "int:5", "absent"]),
    ("bool_int_other_identity", "legacy_bool_int_preamble", "result = 5\n___assertIsNot(1, 0)\nafter = 9\n",
     ["unsupported", "int:5", "absent"]),
    ("bool_int_ordinary_read", "legacy_bool_int_builtin", """def callback():
    assert int
___assertRaises(AssertionError, callback)
""", ["unsupported", "absent", "absent"]),
    ("callable_len_alias", "legacy_bool_callable_builtin", """saved_len = len
len = 7
result = callable(saved_len)
___assertIs(result, True)
___assertIs(callable(len), False)
after = 9
""", ["normal", "bool:True", "int:9"]),
    ("callable_shadow", "legacy_bool_callable_preamble", """result = 5
callable = 7
result = callable(len)
after = 9
""", ["TypeError", "int:5", "absent"]),
    ("assert_is_shadow", "legacy_bool_callable_builtin", """result = 5
___assertIs = 7
___assertIs(callable(len), True)
after = 9
""", ["TypeError", "int:5", "absent"]),
    ("assert_is_argument_order", "legacy_bool_callable_preamble", """result = 5
___assertIs(callable(len), missing)
after = 9
""", ["NameError:missing", "int:5", "absent"]),
    ("assert_is_distinct", "legacy_bool_callable_builtin", """result = 5
___assertIs(callable(1), True)
after = 9
""", ["AssertionError:bool-pair:false:true", "int:5", "absent"]),
    ("assert_is_mixed", "legacy_bool_callable_preamble", "result = 5\n___assertIs(True, 1)\nafter = 9\n",
     ["unsupported", "int:5", "absent"]),
    ("callable_bool", "legacy_bool_callable_builtin", "result = 5\nresult = callable(True)\nafter = 9\n",
     ["unsupported", "int:5", "absent"]),
    ("len_direct", "legacy_bool_callable_preamble", "result = 5\nresult = len(1)\nafter = 9\n",
     ["unsupported", "int:5", "absent"]),
    ("isinstance_type_aliases", "legacy_bool_isinstance_builtin", """saved_bool = bool
saved_int = int
int = saved_bool
converted = saved_int(False)
result = isinstance(converted, int)
___assertIs(result, False)
___assertIs(isinstance(True, saved_int), True)
after = 9
""", ["normal", "bool:False", "int:9"]),
    ("isinstance_shadow", "legacy_bool_isinstance_preamble", """result = 5
isinstance = 7
result = isinstance(True, bool)
after = 9
""", ["TypeError", "int:5", "absent"]),
    ("isinstance_missing_type", "legacy_bool_isinstance_builtin", """result = 5
___assertIs(isinstance(True, missing_type), missing_argument)
after = 9
""", ["NameError:missing_type", "int:5", "absent"]),
    ("isinstance_argument_order", "legacy_bool_isinstance_preamble", """result = 5
___assertIs(isinstance(False, int), missing_argument)
after = 9
""", ["NameError:missing_argument", "int:5", "absent"]),
    ("isinstance_distinct", "legacy_bool_isinstance_builtin", """result = 5
___assertIs(isinstance(1, bool), True)
after = 9
""", ["AssertionError:bool-pair:false:true", "int:5", "absent"]),
    ("isinstance_shadowed_type", "legacy_bool_isinstance_preamble", """result = 5
bool = 7
result = isinstance(True, bool)
after = 9
""", ["unsupported", "int:5", "absent"]),
    ("isinstance_int_int", "legacy_bool_isinstance_builtin", "result = 5\nresult = isinstance(1, int)\nafter = 9\n",
     ["normal", "bool:True", "int:9"]),
    ("bool_direct", "legacy_bool_isinstance_preamble", "result = 5\nresult = bool(1)\nafter = 9\n",
     ["normal", "bool:True", "int:9"]),
)

NESTED_CALL_NAMES = {
    "bool_direct": ["bool"],
    "isinstance_int_int": ["isinstance"],
    "none_value_tags": [],
    "none_value_left_lookup": [],
    "none_value_right_lookup": [],
    "none_value_arithmetic_profile": [],
    "none_value_failed_assertion": [],
    "literal_truth_selected_types": ["___assertIs"],
    "literal_truth_falsy_selected": [],
    "literal_truth_failed_assertion": [],
    "literal_truth_failure_order": [],
    "literal_chain_typed_bindings": ["___assertIs", "___assertIs"],
    "literal_chain_failed_assertion": [],
    "literal_chain_failure_order": [],
    "literal_tuple_typed_bindings": ["___assertIs", "___assertIs"],
    "literal_tuple_failed_assertion": [],
    "literal_tuple_operand_failure_order": [],
    "literal_conditional_true": ["___assertIs"],
    "literal_conditional_false": [],
    "literal_conditional_missing": [],
    "literal_conditional_assertion": [],
    "literal_conditional_unsupported": [],
    "literal_if_order": [],
    "literal_if_failure": [],
    "literal_if_missing": [],
    "nested_missing_outer": [],
    "nested_returns": ["require_error", "compare_ints", "require_error"],
    "nested_first_failure": ["compare_ints"],
    "nested_missing_argument": ["compare_ints"],
    "nested_assertion": ["compare_ints", "require_error"],
    "nested_unsupported": ["AssertionError"],
    "direct_defined_assertion": ["callback"],
    "direct_live_shadow": ["f"],
    "direct_nested_published": ["f", "compare_ints"],
    "direct_nested_positional_unsupported": ["f"],
    "bool_int_argument_order": ["int"],
    "bool_int_defined_assertion": ["int", "___assertEqual"],
    "callable_len_alias": ["callable", "___assertIs", "callable", "___assertIs"],
    "assert_is_shadow": ["callable", "___assertIs"],
    "assert_is_argument_order": ["callable"],
    "assert_is_distinct": ["callable", "___assertIs"],
    "isinstance_type_aliases": ["saved_int", "isinstance", "___assertIs", "isinstance", "___assertIs"],
    "isinstance_missing_type": ["isinstance"],
    "isinstance_argument_order": ["isinstance"],
    "isinstance_distinct": ["isinstance", "___assertIs"],
}

EXACT_FIXTURE_BINDINGS = {
    "dead_boolean_suffix": '[("after", .bool true), ("result", .bool false)]',
    "dead_boolean_integer_tags": '[("after", .int 7), ("result", .int 0)]',
    "none_value_tags": '[("after", .bool true), ("alias", .none), ("result", .none)]',
    "none_value_left_lookup": '[("result", .none)]',
    "none_value_right_lookup": '[("result", .none)]',
    "none_value_arithmetic_profile": '[("result", .none)]',
    "none_value_failed_assertion": '[("result", .none)]',
    "literal_truth_selected_types": '[("after", .int 9), ("result", .bool true)]',
    "literal_truth_falsy_selected": '[("after", .int 5), ("result", .bool false)]',
    "literal_truth_failed_assertion": '[("result", .int 7)]',
    "literal_truth_failure_order": '[("result", .int 7)]',
    "literal_chain_typed_bindings": '[("after", .bool false), ("result", .bool true)]',
    "literal_chain_failed_assertion": '[("result", .int 7)]',
    "literal_chain_failure_order": '[("result", .int 7)]',
    "closed_sequence_typed": '[("after", .bool false), ("result", .bool true)]',
    "closed_sequence_failed_assertion": '[("result", .int 7)]',
    "closed_sequence_enclosing_lookup": '[("result", .int 7)]',
    "literal_tuple_typed_bindings": '[("after", .bool false), ("result", .bool true)]',
    "literal_tuple_failed_assertion": '[("result", .int 7)]',
    "literal_tuple_operand_failure_order": '[("result", .int 7)]',
    "literal_conditional_true": '[("after", .int 1), ("result", .bool true)]',
    "literal_conditional_false": '[("after", .int 5), ("result", .bool false)]',
    "literal_conditional_missing": '[("result", .int 7)]',
    "literal_conditional_assertion": '[("result", .int 7)]',
    "literal_conditional_unsupported": '[("result", .int 7)]',
    "literal_if_order": '[("after", .int 7), ("kept", .int 7), ("result", .int 7)]',
    "literal_if_failure": '[("result", .int 7)]',
    "literal_if_missing": '[("result", .int 7)]',
    "callable_len_alias": '[("after", .int 9), ("result", .bool true), ("len", .int 7), ("saved_len", .builtin .len)]',
    "callable_shadow": '[("callable", .int 7), ("result", .int 5)]',
    "assert_is_shadow": '[("___assertIs", .int 7), ("result", .int 5)]',
    "assert_is_argument_order": '[("result", .int 5)]',
    "assert_is_distinct": '[("result", .int 5)]',
    "assert_is_mixed": '[("result", .int 5)]',
    "callable_bool": '[("result", .int 5)]',
    "len_direct": '[("result", .int 5)]',
    "isinstance_type_aliases": (
        '[("after", .int 9), ("result", .bool false), ("converted", .int 0),'
        ' ("int", .builtin .bool), ("saved_int", .builtin .int), ("saved_bool", .builtin .bool)]'
    ),
    "isinstance_shadow": '[("isinstance", .int 7), ("result", .int 5)]',
    "isinstance_missing_type": '[("result", .int 5)]',
    "isinstance_argument_order": '[("result", .int 5)]',
    "isinstance_distinct": '[("result", .int 5)]',
    "isinstance_shadowed_type": '[("bool", .int 7), ("result", .int 5)]',
    "isinstance_int_int": '[("after", .int 9), ("result", .bool true)]',
    "bool_direct": '[("after", .int 9), ("result", .bool true)]',
}

IDENTITY_FIXTURE_BINDINGS = {
    "singleton_identity_tags": {"result": False, "after": True},
    "singleton_identity_skipped": {"result": False, "after": None},
    "singleton_identity_left_lookup": {"result": None},
    "singleton_identity_middle_lookup": {"result": None},
    "singleton_identity_tail_lookup": {"result": None},
    "singleton_identity_failed_assertion": {"result": None},
}


def identity_bindings(bindings):
    def tag(value):
        return ".none" if value is None else f".bool {str(value).lower()}"
    return "[" + ", ".join(f"({json.dumps(name)}, {tag(value)})"
                           for name, value in reversed(list(bindings.items()))) + "]"


CPYTHON_FIXTURE_BINDINGS = {
    **IDENTITY_FIXTURE_BINDINGS,
    "closed_sequence_typed": {"result": True, "after": False},
    "closed_sequence_failed_assertion": {"result": 7},
    "closed_sequence_enclosing_lookup": {"result": 7},
    "dead_boolean_suffix": {"result": False, "after": True},
    "dead_boolean_integer_tags": {"result": 0, "after": 7},
    "none_value_tags": {"result": None, "alias": None, "after": True},
    "literal_if_order": {"result": 7, "kept": 7, "after": 7},
    "literal_if_failure": {"result": 7},
    "literal_if_missing": {"result": 7},
    "isinstance_type_aliases": {"after": 9, "result": False, "converted": 0,
                               "int": bool, "saved_int": int, "saved_bool": bool},
}


def assertion(error):
    if not error.args:
        return "AssertionError:empty"
    (argument,) = error.args
    if type(argument) is bool:
        return f"AssertionError:bool:{argument}"
    if type(argument) is list:
        return f"AssertionError:list:{argument!r}"
    if isinstance(argument, tuple):
        if not argument:
            return "AssertionError:tuple:()"
        left, right = argument
        if type(left) is bool and type(right) is bool:
            return f"AssertionError:bool-pair:{str(left).lower()}:{str(right).lower()}"
        return f"AssertionError:pair:{left}:{right}"
    return "AssertionError:text:" + argument


def exception_observation(error):
    if isinstance(error, NameError):
        return "NameError:" + error.name
    if isinstance(error, TypeError):
        return "TypeError"
    return assertion(error)


def cpython(source, profile, *, expected_globals=None, expected_functions=(), expected_warnings=()):
    legacy = profile.startswith("legacy_")
    profile = profile.removeprefix("legacy_")
    bool_int = profile.startswith("bool_int_")
    profile = profile.removeprefix("bool_int_")
    bool_callable = profile.startswith("bool_callable_")
    profile = profile.removeprefix("bool_callable_")
    bool_isinstance = profile.startswith("bool_isinstance_")
    profile = profile.removeprefix("bool_isinstance_")
    caught = []

    def compare_ints(left, right):
        if left != right:
            raise AssertionError((left, right))

    def assert_is_not(left, right):
        assert left is not right, (left, right)

    def assert_is(left, right):
        assert left is right, (left, right)

    def require_error(expected, callback, *arguments):
        try:
            callback(*arguments)
        except expected as error:
            caught.append(exception_observation(error))
            return None
        if profile == "preamble":
            raise AssertionError("did not raise exception")
        raise AssertionError()

    if legacy:
        helpers = {"___assertRaises": require_error, "___assertEqual": compare_ints}
        classes = {"AssertionError": AssertionError}
    else:
        helpers = {"require_error": require_error, "compare_ints": compare_ints}
        classes = {"AssertionError": AssertionError, "TypeError": TypeError, "NameError": NameError}
    if bool_int:
        classes["int"] = int
        helpers["___assertIsNot"] = assert_is_not
    if bool_callable:
        classes.update(callable=callable, len=len)
    if bool_isinstance:
        classes.update(isinstance=isinstance, bool=bool, int=int)
    if bool_callable or bool_isinstance:
        helpers["___assertIs"] = assert_is
    if profile == "builtin":
        namespace = {"__builtins__": classes | helpers}
    elif profile == "preamble":
        namespace = {"__builtins__": classes, **helpers}
    else:
        namespace = {"__builtins__": {}}
    initial = namespace.copy()
    completion = "normal"
    with redirect_stdout(StringIO()) as stdout, redirect_stderr(StringIO()) as stderr:
        with warnings.catch_warnings(record=True) as emitted:
            warnings.simplefilter("always")
            unit = compile(source, "<seeded fixture>", "exec", dont_inherit=True, optimize=0)
        actual_warnings = tuple((w.category.__name__, w.lineno, str(w.message)) for w in emitted)
        assert actual_warnings == expected_warnings, actual_warnings
        try:
            exec(unit, namespace)
        except (NameError, TypeError, AssertionError) as error:
            completion = exception_observation(error)
    assert not stdout.getvalue() and not stderr.getvalue()
    if expected_globals is not None:
        assert all(type(namespace.get(name)) is FunctionType for name in expected_functions)
        assert {key: value for key, value in namespace.items() if key not in expected_functions} == initial | expected_globals
    bindings = []
    for name in ("result", "after"):
        if name not in namespace:
            bindings.append("absent")
        elif namespace[name] is None:
            bindings.append("None")
        elif type(namespace[name]) is bool:
            bindings.append(f"bool:{namespace[name]}")
        elif type(namespace[name]) is FunctionType:
            bindings.append("function")
        else:
            assert type(namespace[name]) is int
            bindings.append(f"int:{namespace[name]}")
    return [completion, *bindings, *caught]


def pinned_source(checkout, path, sha256):
    raw = (checkout / path).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == sha256, path
    return raw.decode("utf-8")


def pinned_truth_helper(checkout):
    path = "tests/python/evaluation/programs.py"
    digest = "55091465bd9ff2b6f784d31b48798f50dfffb98b712e22c96fe4092b6e4eb37f"
    harness = pinned_source(checkout, path, digest)
    preamble, = (ast.literal_eval(stmt.value) for stmt in ast.parse(harness).body
                 if isinstance(stmt, ast.Assign) and any(
                     isinstance(target, ast.Name) and target.id == "LAMBDA_PY_PREAMBLE"
                     for target in stmt.targets))
    namespace = {}
    exec(compile(preamble, path, "exec", dont_inherit=True, optimize=0), namespace)
    return namespace["___assertTrue"]


def guard_observation(profile, expected):
    return f"#guard inspect pythonSource {json.dumps(profile)} == some {json.dumps(expected)}"


def replay_upstream_nested(checkout, shared, source_path, lean_path):
    rows = []
    for filename, sha256, empty_name, seeded_name, seeded_calls in UPSTREAM_NESTED:
        path = f"{UPSTREAM_BOOL_DIR}/{filename}"
        source = pinned_source(checkout, path, sha256)
        shared["emit"](source_path, lean_path, source)
        guards = [f'#guard ordinaryOutcome pythonSource == some ("NameError:{empty_name}", none)']
        completions = {}
        for profile, missing_name, calls in (
            ("empty", empty_name, []),
            ("legacy_builtin", seeded_name, seeded_calls),
            ("legacy_preamble", seeded_name, seeded_calls),
        ):
            expected = ["NameError:" + missing_name, "absent", "absent"]
            assert cpython(source, profile, expected_globals={}) == expected, (path, profile)
            name = json.dumps(profile)
            guards.extend((
                guard_observation(profile, expected),
                f"#guard callNames pythonSource {name} == some {json.dumps(calls)}",
                f"#guard exactGlobals pythonSource {name}",
            ))
            completions[profile] = expected[0]
        projection = {}
        for profile in BOOL_INT_PROFILES:
            completion = "normal" if filename == "bool-int.py" else "NameError:___assertIs"
            expected = [completion, "absent", "absent"]
            assert cpython(source, profile, expected_globals={}) == expected, (path, profile)
            name = json.dumps(profile)
            guards.extend((guard_observation(profile, expected), f"#guard exactGlobals pythonSource {name}"))
            if completion == "normal":
                call_values = [
                    '("int", .int 0)', '("___assertEqual", .none)',
                    '("int", .int 0)', '("___assertIsNot", .none)',
                    '("int", .int 1)', '("___assertEqual", .none)',
                    '("int", .int 1)', '("___assertIsNot", .none)',
                ]
                guards.append(f"#guard callValues pythonSource {name} = some [{', '.join(call_values)}]")
            else:
                guards.append(f"#guard callNames pythonSource {name} == some []")
            projection[profile] = completion
        callable_projection = {}
        for profile in BOOL_CALLABLE_PROFILES:
            completion, calls = {
                "bool-callable.py": ("normal", ["callable", "___assertIs", "callable", "___assertIs"]),
                "bool-int.py": ("NameError:int", ["int"]),
                "bool-isinstance.py": ("NameError:isinstance", ["isinstance"]),
            }[filename]
            expected = [completion, "absent", "absent"]
            assert cpython(source, profile, expected_globals={}) == expected, (path, profile)
            name = json.dumps(profile)
            guards.extend((
                guard_observation(profile, expected),
                f"#guard exactGlobals pythonSource {name}",
                f"#guard callNames pythonSource {name} == some {json.dumps(calls)}",
            ))
            if completion == "normal":
                guards.append(
                    f'#guard callValues pythonSource {name} = some [("callable", .bool true), '
                    '("___assertIs", .none), ("callable", .bool false), ("___assertIs", .none)]'
                )
            callable_projection[profile] = {"completion": completion, "calls": calls, "user_bindings": {}}
        isinstance_projection = {}
        instance_results = [True, True, True, True, False, False]
        for profile in BOOL_ISINSTANCE_PROFILES:
            completion, calls = {
                "bool-callable.py": ("NameError:callable", ["callable"]),
                "bool-int.py": ("NameError:___assertIsNot", ["int", "___assertEqual"]),
                "bool-isinstance.py": ("normal", ["isinstance", "___assertIs"] * len(instance_results)),
            }[filename]
            expected = [completion, "absent", "absent"]
            assert cpython(source, profile, expected_globals={}) == expected, (path, profile)
            name = json.dumps(profile)
            guards.extend((
                guard_observation(profile, expected),
                f"#guard exactGlobals pythonSource {name}",
                f"#guard callNames pythonSource {name} == some {json.dumps(calls)}",
            ))
            observation = {"completion": completion, "calls": calls, "user_bindings": {}}
            if completion == "normal":
                call_values = [
                    entry for value in instance_results
                    for entry in (f'("isinstance", .bool {str(value).lower()})', '("___assertIs", .none)')
                ]
                guards.append(f"#guard callValues pythonSource {name} = some [{', '.join(call_values)}]")
                observation["returns"] = [result for value in instance_results for result in (value, None)]
            isinstance_projection[profile] = observation
        shared["check_lean"](lean_path, LEAN + "\n".join(guards), extra_imports=IMPORTS)
        rows.append({"path": path, "sha256": sha256, "completions": completions,
                     "bool_int_projection": projection, "bool_callable_projection": callable_projection,
                     "bool_isinstance_projection": isinstance_projection})
    return rows


def replay_upstream_scalars(checkout, shared, source_path, lean_path):
    rows = []
    cases = (
        (UPSTREAM_ASSIGN_CASE, UPSTREAM_ASSIGN_SHA256, {"x": 5}),
        (UPSTREAM_ASSERT_NOT_CASE, UPSTREAM_ASSERT_NOT_SHA256, {}),
        (UPSTREAM_LITERAL_IF_CASE, UPSTREAM_LITERAL_IF_SHA256, {}),
        (UPSTREAM_CONDITIONAL_EXPR_CASE, UPSTREAM_CONDITIONAL_EXPR_SHA256, {}),
        (UPSTREAM_NONE_VALUE_CASE, UPSTREAM_NONE_VALUE_SHA256, {"ret": 3}),
        (UPSTREAM_SINGLETON_IDENTITY_CASE, UPSTREAM_SINGLETON_IDENTITY_SHA256, {}),
        (UPSTREAM_DEAD_BOOLEAN_CASE, UPSTREAM_DEAD_BOOLEAN_SHA256, {}),
        (UPSTREAM_CLOSED_SEQUENCE_CASE, UPSTREAM_CLOSED_SEQUENCE_SHA256, {}),
        *((path, sha256, {}) for path, sha256 in UPSTREAM_NO_OP),
        *((path, sha256, {}) for path, sha256 in UPSTREAM_LITERAL_INDEXING),
        *((path, sha256, {}) for path, sha256 in UPSTREAM_LITERAL_TUPLE_COMPARISONS),
        *((path, sha256, {}) for path, sha256 in UPSTREAM_LITERAL_COMPARISON_CHAINS),
        *((path, sha256, {}) for path, sha256 in UPSTREAM_LITERAL_TRUTH),
    )
    for path, sha256, bindings in cases:
        source = pinned_source(checkout, path, sha256)
        shared["emit"](source_path, lean_path, source)
        assert len(bindings) <= 1
        observed, value = next(iter(bindings.items()), ("x", None))
        expected_binding = "none" if value is None else f"some {value}"
        seeded_bindings = "[]" if value is None else f"[({json.dumps(observed)}, .int {value})]"
        guards = [f'#guard ordinaryOutcome pythonSource {json.dumps(observed)} == some ("normal", {expected_binding})']
        if path == UPSTREAM_ASSERT_NOT_CASE:
            guards.append("#guard equalityBeforeAssertNot pythonSource")
        syntax_warnings = UPSTREAM_SCALAR_WARNINGS.get(path, ())
        for profile in ("empty", "legacy_builtin", "legacy_preamble", *OPT_IN_PROFILES):
            expected = ["normal", "absent", "absent"]
            assert cpython(source, profile, expected_globals=bindings,
                           expected_warnings=syntax_warnings) == expected, (path, profile)
            name = json.dumps(profile)
            if path in (UPSTREAM_SINGLETON_IDENTITY_CASE, UPSTREAM_DEAD_BOOLEAN_CASE, UPSTREAM_CLOSED_SEQUENCE_CASE):
                guards.append(f'#guard scalarEvidence pythonSource {name} "normal" []')
            if path in (UPSTREAM_DEAD_BOOLEAN_CASE, UPSTREAM_CLOSED_SEQUENCE_CASE):
                count = 8 if path == UPSTREAM_DEAD_BOOLEAN_CASE else 1
                assertions = ast.parse(source).body
                assert len(assertions) == count and all(isinstance(stmt, ast.Assert) for stmt in assertions)
                assert all(eval(compile(ast.Expression(stmt.test), path, "eval", optimize=0),
                                {"__builtins__": {}}) is True for stmt in assertions)
                guards.append(f"#guard trueAssertionOperands pythonSource {name} {count}")
            guards.extend((
                guard_observation(profile, expected),
                f"#guard exactGlobals pythonSource {name} {seeded_bindings}",
                f"#guard callNames pythonSource {name} == some []",
            ))
        shared["check_lean"](lean_path, LEAN + "\n".join(guards), extra_imports=IMPORTS)
        row = {"path": path, "sha256": sha256, "all_profiles": "normal", "user_bindings": bindings}
        if syntax_warnings:
            row["cpython_compile_warnings"] = syntax_warnings
        rows.append(row)
    return rows


def replay_upstream_publication(checkout, shared, source_path, lean_path):
    source = pinned_source(checkout, UPSTREAM_PUBLICATION_CASE, UPSTREAM_PUBLICATION_SHA256)
    shared["emit"](source_path, lean_path, source)
    guards = ['#guard ordinaryOutcome pythonSource == some ("NameError:___assertRaises", none)']
    observations = {}
    for profile in ("empty", "legacy_builtin", "legacy_preamble", *OPT_IN_PROFILES):
        empty = profile == "empty"
        cpython_expected = (["NameError:___assertRaises", "absent", "absent"] if empty
                             else ["normal", "absent", "absent", "AssertionError:empty"])
        assert cpython(source, profile, expected_globals={}, expected_functions=("failing_function",)) == cpython_expected
        seeded = "NameError:___assertRaises" if empty else "normal"
        phase = "callee lookup" if empty else "caught callback assertion"
        guards.extend((
            guard_observation(profile, cpython_expected),
            f"#guard publicationReceipt pythonSource {json.dumps(profile)} == some {json.dumps(phase)}",
        ))
        observations[profile] = {"cpython": cpython_expected[0], "seeded": seeded, "phase": phase,
                                 "user_bindings": {"failing_function": "function"}}
    shared["check_lean"](lean_path, LEAN + "\n".join(guards), extra_imports=IMPORTS)
    return {"path": UPSTREAM_PUBLICATION_CASE, "sha256": UPSTREAM_PUBLICATION_SHA256, "profiles": observations}


def replay_upstream_direct_discard(checkout, shared, source_path, lean_path):
    source = pinned_source(checkout, UPSTREAM_DIRECT_DISCARD_CASE, UPSTREAM_DIRECT_DISCARD_SHA256)
    shared["emit"](source_path, lean_path, source)
    (published, _) = ast.parse(source).body
    assert isinstance(published, ast.FunctionDef)
    guards = ['#guard ordinaryOutcome pythonSource == some ("normal", none)']
    observations = {}
    for profile in ("empty", "legacy_builtin", "legacy_preamble"):
        expected = ["normal", "absent", "absent"]
        assert cpython(source, profile, expected_globals={}, expected_functions=(published.name,)) == expected
        guards.append(f"#guard directDiscardReceipt pythonSource {json.dumps(profile)} = some (1, 5)")
        observations[profile] = {"cpython": "normal", "seeded": "normal", "user_bindings": ["published function"],
                                 "receipt": {"result": "None", "caught": None}, "heap": {"next": 1, "cell_0": 5}}
    shared["check_lean"](lean_path, LEAN + "\n".join(guards), extra_imports=IMPORTS)
    return {"path": UPSTREAM_DIRECT_DISCARD_CASE, "sha256": UPSTREAM_DIRECT_DISCARD_SHA256, "profiles": observations}


def replay_upstream(checkout, shared, source_path, lean_path):
    revision = subprocess.check_output(
        ["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True
    ).strip()
    assert revision == UPSTREAM_REVISION, revision
    source = pinned_source(checkout, UPSTREAM_CASE, UPSTREAM_SHA256)
    shared["emit"](source_path, lean_path, source)
    guards = """
#guard ordinaryOutcome pythonSource == some ("NameError:___assertRaises", none)
#guard inspect pythonSource "empty" == some ["NameError:___assertRaises", "absent", "absent"]
#guard exactGlobals pythonSource "empty"
"""
    assert cpython(source, "empty", expected_globals={}) == ["NameError:___assertRaises", "absent", "absent"]
    for profile in ("legacy_builtin", "legacy_preamble", *OPT_IN_PROFILES):
        expected = ["normal", "absent", "absent", "AssertionError:pair:1:2"]
        assert cpython(source, profile, expected_globals={}) == expected, profile
        name = json.dumps(profile)
        guards += "\n".join((
            guard_observation(profile, expected),
            f"#guard singleNoneReturn pythonSource {name}",
            f"#guard exactGlobals pythonSource {name}",
            "",
        ))
    shared["check_lean"](lean_path, LEAN + guards, extra_imports=IMPORTS)
    return {
        "revision": revision,
        "sha256": UPSTREAM_SHA256,
        "empty": "NameError:___assertRaises",
        "builtin": "normal, None, caught AssertionError((1, 2))",
        "preamble_projection": "normal, None, caught AssertionError((1, 2))",
        "nested": replay_upstream_nested(checkout, shared, source_path, lean_path),
        "scalars": replay_upstream_scalars(checkout, shared, source_path, lean_path),
        "publication": replay_upstream_publication(checkout, shared, source_path, lean_path),
        "direct_discard": replay_upstream_direct_discard(checkout, shared, source_path, lean_path),
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path, help="also replay cases from the pinned public checkout")
    args = parser.parse_args()
    shared = runpy.run_path(str(Path(__file__).resolve().parent.parent / "source-scope/check_intake.py"))
    observations = {}
    lean_only = []
    upstream = None
    with tempfile.TemporaryDirectory() as tmp:
        source_path = Path(tmp) / "Example.py"
        lean_path = Path(tmp) / "Example.lean"
        for name, profile, source, expected in FIXTURES:
            shared["emit"](source_path, lean_path, source)
            check = guard_observation(profile, expected)
            if name in NESTED_CALL_NAMES:
                check += f"\n#guard callNames pythonSource {json.dumps(profile)} == some {json.dumps(NESTED_CALL_NAMES[name])}"
            if name in EXACT_FIXTURE_BINDINGS:
                check += f"\n#guard exactGlobals pythonSource {json.dumps(profile)} {EXACT_FIXTURE_BINDINGS[name]}"
            if name in IDENTITY_FIXTURE_BINDINGS:
                bindings = identity_bindings(IDENTITY_FIXTURE_BINDINGS[name])
                check += f"\n#guard scalarEvidence pythonSource {json.dumps(profile)} {json.dumps(expected[0])} {bindings}"
            if name.startswith("closed_sequence_"):
                bindings = EXACT_FIXTURE_BINDINGS[name]
                check += f"\n#guard scalarEvidence pythonSource {json.dumps(profile)} {json.dumps(expected[0])} {bindings}"
            if name in ("dead_boolean_suffix", "dead_boolean_integer_tags"):
                check += f"\n#guard callNames pythonSource {json.dumps(profile)} == some []"
            if name == "empty":
                check += "\n" + AUDIT
            shared["check_lean"](lean_path, LEAN + check, extra_imports=IMPORTS)
            if expected[0] == "unsupported":
                lean_only.append(name)
            else:
                assert cpython(source, profile, expected_globals=CPYTHON_FIXTURE_BINDINGS.get(name)) == expected, name
            observations[name] = expected
        for profile in ("empty", "legacy_builtin", "legacy_preamble"):
            for value, completion, after in ((4, "normal", 9), (3, "AssertionError:empty", None)):
                source = ADJACENT_KEYWORD % value
                residual = {"result": 5} if after is None else {"result": 5, "after": after}
                expected = [completion, "int:5", "absent" if after is None else f"int:{after}"]
                assert cpython(source, profile, expected_globals=residual, expected_functions=("probe",)) == expected
                shared["emit"](source_path, lean_path, source)
                check = guard_observation(profile, expected)
                check += f"\n#guard adjacentKeywordEvidence pythonSource {json.dumps(profile)} {value}"
                shared["check_lean"](lean_path, LEAN + check, extra_imports=IMPORTS)
                observations[f"adjacent_keyword_{profile}_{value}"] = expected
        for profile in ("empty", "builtin", "preamble"):
            for operand, succeeds in (("increment", True), ("probe", False)):
                source = ADDITION % operand
                if succeeds:
                    source = "increment = 1\n" + source
                residual = {"result": 5, "after": 9, "increment": 1} if succeeds else {"result": 5}
                expected = ["normal", "int:5", "int:9"] if succeeds else ["TypeError", "int:5", "absent"]
                assert cpython(source, profile, expected_globals=residual, expected_functions=("probe",)) == expected
                shared["emit"](source_path, lean_path, source)
                check = guard_observation(profile, expected)
                check += f"\n#guard additionEvidence pythonSource {json.dumps(profile)} {str(succeeds).lower()}"
                shared["check_lean"](lean_path, LEAN + check, extra_imports=IMPORTS)
                observations[f"closure_addition_{profile}_{succeeds}"] = expected
        shared["emit"](source_path, lean_path, "def probe(value): pass\nprobe(4)\nafter = 9\n")
        shared["check_lean"](lean_path, LEAN + guard_observation("empty", ["unsupported", "absent", "absent"]),
                             extra_imports=IMPORTS)
        if args.upstream is not None:
            upstream = replay_upstream(args.upstream, shared, source_path, lean_path)
    print(json.dumps({"cpython": sys.version.split()[0], "observations": observations,
                      "lean_only": lean_only, "upstream": upstream}))
