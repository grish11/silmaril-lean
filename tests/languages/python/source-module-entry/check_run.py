# SPDX-License-Identifier: MIT
"""Compare actual Python modules with source lowering and the Core runner."""

import ast
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile


FIXTURES = (
    ("seed_and_overwrite", """global result
result = seed + True
assert result == 41
result = result + 1
assert result == 42
""", {"seed": 40, "untouched": True}, {"seed": 40, "untouched": True, "result": 42},
     "normal", ".normal", 3),
    ("failed_assertion", """before = 1
assert False
after = 2
""", {}, {"before": 1, "after": None}, "AssertionError", ".raised .assertionError", 2),
    ("unbound_global", """before = 1
assert missing
after = 2
""", {}, {"before": 1, "missing": None, "after": None},
     "NameError", '.raised (.nameError "missing")', 2),
    ("arithmetic_failure", """before = 1
assert 1 // 0
after = 2
""", {}, {"before": 1, "after": None}, "ZeroDivisionError", ".raised (.arithmetic .zeroDivisionError)", 2),
    ("signed_division", """result = -7 // 3
assert result == -3
assert True == 1
""", {}, {"result": -3}, "normal", ".normal", 2),
    ("literal_sequence_indexing", """result = [-7, 4, 9][-3]
assert (8, -7)[0] == 8
""", {}, {"result": -7}, "normal", ".normal", 2),
    ("literal_dictionary_get", """result = {1: 2, True: 7}.get(1, 9)
assert {}.get(False) is None
assert result == 7
""", {}, {"result": 7}, "normal", ".normal", 2),
    ("indexed_assertion_failure", """before = 1
assert (2, 4)[-1] == 2
after = 2
""", {}, {"before": 1, "after": None}, "AssertionError", ".raised .assertionError", 2),
    ("literal_if_order", """result = 1
if -1:
    result = 2
    kept = result
    pass
else:
    assert missing
if False:
    result = 8
else:
    result = kept
assert result == 2
""", {}, {"result": 2, "kept": 2}, "normal", ".normal", 5),
    ("literal_if_failure", """result = 1
if False:
    assert missing
else:
    result = 2
    assert False
    result = 3
after = 9
""", {}, {"result": 2, "after": None}, "AssertionError", ".raised .assertionError", 3),
    ("literal_if_no_else", """if 0:
    bad = 1
result = 2
""", {}, {"result": 2, "bad": None}, "normal", ".normal", 2),
    ("literal_conditional_types", """truth = False if -1 else missing
number = 1 // 0 if 0 else 0
assert not_reached if False else 1
""", {}, {"truth": False, "number": 0}, "normal", ".normal", 3),
    ("literal_conditional_error", """result = 7
result = missing if 0 else 1 // 0
after = 9
""", {}, {"result": 7, "after": None}, "ZeroDivisionError", ".raised (.arithmetic .zeroDivisionError)", 2),
    ("literal_tuple_boolean_results", """same = (True, -2, False) == (1, -2, 0)
different = (1, 2) == (2, 1)
member = -2 in (True, -2)
absent = 1 not in ()
assert () == ()
assert True in (1,)
assert 1 not in (False,)
""", {}, {"same": True, "different": False, "member": True, "absent": True}, "normal", ".normal", 5),
    ("literal_tuple_operand_failure_order", """result = 7
result = (1 in (True,)) == (missing + (1 // 0))
after = 9
""", {}, {"result": 7, "after": None}, "NameError", '.raised (.nameError "missing")', 2),
    ("literal_chain_boolean_results", """mixed = -1 < False <= True == 1
middle = 0 < 2 > 1
stopped = 1 < 0 < -1
reached = 0 < 1 > 2
assert -2 < 0 <= 1 != 2
""", {}, {"mixed": True, "middle": True, "stopped": False, "reached": False}, "normal", ".normal", 5),
    ("literal_chain_enclosing_failure_order", """result = 7
result = (0 < 2 > 1) == (missing + (1 // 0))
after = 9
""", {}, {"result": 7, "after": None}, "NameError", '.raised (.nameError "missing")', 2),
    ("literal_truth_types", """a = 0 or True
b = False and 7
c = True and -2 and 9
d = 0 or False or -1
e = not ()
assert [False]
assert not None
""", {}, {"a": True, "b": False, "c": 9, "d": -1, "e": True}, "normal", ".normal", 6),
    ("literal_truth_failure", """result = 7
assert []
after = 9
""", {}, {"result": 7, "after": None}, "AssertionError", ".raised .assertionError", 2),
    ("literal_truth_enclosing_failure", """result = 7
result = (0 or -2) == (missing + (1 // 0))
after = 9
""", {}, {"result": 7, "after": None}, "NameError", '.raised (.nameError "missing")', 2),
    ("none_scalar_rebind", """result = None
assert result == None
assert result != 0
result = 3
assert None != result
assert False == 0
""", {}, {"result": 3}, "normal", ".normal", 3),
    ("none_right_read_failure", """result = 7
result = None != missing
after = 9
""", {}, {"result": 7, "after": None}, "NameError", '.raised (.nameError "missing")', 2),
    ("none_arithmetic_read_precedes_profile", """result = 7
result = None + missing
after = 9
""", {}, {"result": 7, "after": None}, "NameError", '.raised (.nameError "missing")', 2),
    ("singleton_identity_typed", """result = None is False
after = False is not True is (1 == True)
assert None is None
""", {}, {"result": False, "after": True}, "normal", ".normal", 3),
    ("singleton_identity_skips_missing", """result = False is True is (missing == 0)
""", {}, {"result": False}, "normal", ".normal", 2),
    ("singleton_identity_reached_missing", """result = 7
result = False is not True is (missing == 0)
after = 9
""", {}, {"result": 7, "after": None}, "NameError", '.raised (.nameError "missing")', 2),
    ("boolean_dead_suffix", """result = True and False and (5 / 0) and (1 // 0 + (False or -2))
after = False or True or (5 / 0)
assert (False and (True and (1 / 0))) is False
""", {}, {"result": False, "after": True}, "normal", ".normal", 3),
    ("boolean_dead_suffix_integer_tag", """result = 0 and (5 / 0)
after = 7 or (5 / 0)
""", {}, {"result": 0, "after": 7}, "normal", ".normal", 3),
    ("closed_sequence_typed", """result = [] + [True] + [-2, False] == [1, -2, 0]
after = (True,) + (False,) != (1, 0)
assert [1, 2] != (1, 2)
assert [1] != [1, 1]
assert ([4, 3] + []) == [4, 3]
""", {}, {"result": True, "after": False}, "normal", ".normal", 3),
    ("closed_sequence_assertion_failure", """result = 7
assert ([1, 2] + [3]) == [1, 3, 2]
after = 9
""", {}, {"result": 7, "after": None}, "AssertionError", ".raised .assertionError", 2),
    ("closed_sequence_enclosing_lookup", """result = 7
result = (([1] + [2]) == [1, 2]) == missing
after = 9
""", {}, {"result": 7, "after": None}, "NameError", '.raised (.nameError "missing")', 2),
)

UNSUPPORTED_INDEXING = (
    "result = [7][1]\n",
    "result = (7,)[-2]\n",
    "result = [][0]\n",
    "result = [7][True]\n",
    "index = 0\nresult = [7][index]\n",
    "value = 7\nresult = [value][0]\n",
    "result = [7, 1 // 0][0]\n",
    "result = [7][:1]\n",
)

REJECTED_BRANCHES = (
    ("flag = 1\nif flag: pass\n", ".statementProfile"),
    ("if [1]: pass\n", ".statementProfile"),
    ("if 0:\n    global hidden\n", ".statementProfile"),
    ("if False:\n    def hidden(): pass\n", ".statementProfile"),
    ("if False:\n    class Hidden: pass\n", ".statementProfile"),
    ("if False:\n    hidden = lambda: 1\n", ".expressionProfile"),
    ("if False:\n    assert True, 'message'\n", ".statementProfile"),
    ("if False:\n    if True: pass\n", ".statementProfile"),
    ("if False:\n    nonlocal hidden\n", '.scope ⟨[], .nonlocalInModule "hidden"⟩'),
    ("hidden = 1\nif False:\n    global hidden\n",
     '.scope ⟨[], .boundBeforeDirective "hidden" .global_⟩'),
    ("flag = 1\nresult = 2 if flag else 3\n", ".expressionProfile"),
    ("result = 2 if True else (lambda: 3)\n", ".expressionProfile"),
    ("result = f() if False else 3\n", ".expressionProfile"),
    ("result = 1 if True else [3][1]\n", ".expressionProfile"),
    ("result = (1, unknown) == (1, 2)\n", ".expressionProfile"),
    ("result = (1,) + (2,)\n", ".expressionProfile"),
    ("result = ([1] + [2]) in ([1, 2],)\n", ".expressionProfile"),
    ("result = ([1],) == ([1],)\n", ".expressionProfile"),
    ("result = (1,) in ((1,),)\n", ".expressionProfile"),
    ("result = 1 in (*other,)\n", ".expressionProfile"),
    ("result = 1 in (f(),)\n", ".expressionProfile"),
    ("result = 1 in (1,) == (1,)\n", ".expressionProfile"),
    ("result = 0 > 1 < missing\n", ".expressionProfile"),
    ("result = 0 > 1 < (1 // 0)\n", ".expressionProfile"),
    ("result = 0 > 1 is 2\n", ".expressionProfile"),
    ("result = 0 > 1 < 2.0\n", ".expressionProfile"),
    ("result = 0 < probe() < 2\n", ".expressionProfile"),
    ("result = 0 < 1\n", ".expressionProfile"),
    ("result = False and missing\n", ".expressionProfile"),
    ("result = True or (False and missing)\n", ".expressionProfile"),
    ("result = True or (5 / (lambda: 0))\n", ".expressionProfile"),
    ("result = False and (5 / probe())\n", ".expressionProfile"),
    ("assert (missing,)\n", ".expressionProfile"),
    ("assert [probe()]\n", ".expressionProfile"),
    ("result = (1,)\n", ".expressionProfile"),
    ("assert [()]\n", ".expressionProfile"),
    ("result = 1 is 1\n", ".expressionProfile"),
    ('result = "same" is "same"\n', ".expressionProfile"),
    ("result = 1000 is 1000\n", ".expressionProfile"),
    ("result = 'text' is 'text'\n", ".expressionProfile"),
    ("result = False is True is 1\n", ".expressionProfile"),
    ("result = False is True is (5 / 0 == 0)\n", ".expressionProfile"),
    ("result = False is True < False\n", ".expressionProfile"),
    ("result = current is None\n", ".expressionProfile"),
)

CPYTHON = """
import json
import sys
import tokenize

names = json.loads(sys.argv[2])
namespace = {"__builtins__": {}, **json.loads(sys.argv[3])}
completion = "normal"
try:
    with tokenize.open(sys.argv[1]) as source:
        exec(compile(source.read(), sys.argv[1], "exec", optimize=0), namespace)
except (AssertionError, NameError, ZeroDivisionError) as error:
    completion = type(error).__name__

print(json.dumps([completion, {name: namespace.get(name) for name in names}]))
"""

LEAN = """
open Silmaril.Languages.Python
open Silmaril.Languages.Python.Compile.ModuleEntry.Run

private def observation (source : Module) (bindings : List (String × Core.Module.Value))
    (names : List String) : Option (Core.Module.Completion × List (Option Core.Module.Value) × Nat) := do
  let compiled ← (compile source (Core.Module.Globals.ofBindings bindings)).toOption
  let (log, state) := compiled.run
  match state with
  | .finished final => some (final.completion, names.map final.globals.lookup, log.length)
  | .running .. => none

private def unsupportedIndex (source : Module) : Bool :=
  match Compile.ModuleEntry.check source with
  | .error .expressionProfile => true
  | _ => false

private def rejection (source : Module) : Option Compile.ModuleEntry.Error :=
  match Compile.ModuleEntry.check source with
  | .error error => some error
  | _ => none
"""


def lean_value(value):
    if isinstance(value, bool):
        return ".bool true" if value else ".bool false"
    assert isinstance(value, int), value
    return f".int ({value})"


def check_chain_order():
    visits = []

    def probe(value):
        visits.append(value)
        return value

    namespace = {"__builtins__": {}, "probe": probe}
    cases = (
        ("probe(0) < probe(2) > probe(1)", True, [0, 2, 1]),
        ("probe(1) < probe(0) < probe(-1)", False, [1, 0]),
        ("0 > 1 < missing", False, []),
        ("0 > 1 < (1 // 0)", False, []),
        ("probe(False) is not probe(True) is probe(True)", True, [False, True, True]),
        ("probe(False) is probe(True) is probe(None)", False, [False, True]),
    )
    for source, result, expected_visits in cases:
        visits.clear()
        expression = compile(source, "<comparison chain>", "eval", dont_inherit=True, optimize=0)
        assert eval(expression, namespace) is result, source
        assert visits == expected_visits, source


REACHED_DIVISION = (
    ("True and 5 / 0", ZeroDivisionError, None),
    ("False or 5 / 0", ZeroDivisionError, None),
    ("False or False or (5 / 0)", ZeroDivisionError, None),
    ("True and (True and 5 / 0) and False", ZeroDivisionError, None),
    ("True and 5 / 2", None, 2.5),
    ("False or 5 // 0", ZeroDivisionError, None),
)


def boolean_rejection_fixtures():
    for expression, error, expected in REACHED_DIVISION:
        source = f"before = 7\nresult = {expression}\nafter = 9\n"
        namespace = {"__builtins__": {}}
        try:
            exec(compile(source, "<reached Boolean operand>", "exec", optimize=0), namespace)
        except ZeroDivisionError as raised:
            assert type(raised) is error and namespace == {"__builtins__": {}, "before": 7}
        else:
            assert error is None and type(namespace["result"]) is float and namespace["result"] == expected
        yield source, "#guard rejection pythonSource == some .expressionProfile"

    guards = ""
    for arity in (0, 1):
        tree = ast.parse("result = True or False")
        values = [ast.Constant(value=False)] * arity
        tree.body[0].value.values[1] = ast.BoolOp(op=ast.And(), values=values)
        try:
            compile(ast.fix_missing_locations(tree), "<malformed dead operand>", "exec", optimize=0)
        except ValueError as raised:
            assert str(raised) == "BoolOp with less than 2 values"
        else:
            raise AssertionError("CPython accepted a malformed Boolean node")
        operands = "[.boolean false]" if arity else "[]"
        guards += (
            f'#guard rejection ⟨[.assign "result" (.booleanOp .or_ [.boolean true,'
            f' .booleanOp .and_ {operands}])]⟩ == some .expressionProfile\n'
            f'#guard rejection ⟨[.assign "result" (.booleanOp .and_ {operands})]⟩ == some .expressionProfile\n'
        )
    yield "result = True or 5 / 0\n", guards


SEQUENCE_ERRORS = (
    ("([0] + [left_missing]) == (right_missing,)", NameError, "left_missing"),
    ("([0] + [1]) == (right_missing,)", NameError, "right_missing"),
    ("([0] + [left_missing]) == [1]", NameError, "left_missing"),
    ("([0] + (1,)) == [right_missing]", TypeError, None),
    ("([0] + [1 // 0]) == [3]", ZeroDivisionError, None),
)


def sequence_rejection_fixtures():
    for expression, error, name in SEQUENCE_ERRORS:
        source = f"result = 7\nresult = {expression}\nafter = 9\n"
        namespace = {"__builtins__": {}}
        try:
            exec(compile(source, "<open sequence comparison>", "exec", optimize=0), namespace)
        except error as raised:
            assert type(raised) is error and getattr(raised, "name", None) == name
            assert namespace == {"__builtins__": {}, "result": 7}
        else:
            raise AssertionError(f"CPython completed {expression!r}")
        yield source, "#guard rejection pythonSource == some .expressionProfile"


if __name__ == "__main__":
    check_chain_order()
    shared = runpy.run_path(str(Path(__file__).resolve().parent.parent / "source-scope/check_intake.py"))
    imports = (
        "import Silmaril.Languages.Python.Compile.ModuleEntry.Run.Thms",
        "meta import Silmaril.Languages.Python.Compile.ModuleEntry.Run.Defs",
        "meta import Silmaril.Languages.Python.Core.Module.Defs",
    )
    observations = {}
    fixtures = []
    with tempfile.TemporaryDirectory() as tmp:
        for name, source, seeds, namespace, completion, observed, events in FIXTURES:
            python_file = Path(tmp) / f"{name}.py"
            python_file.write_text(source, encoding="utf-8")
            names = list(namespace)
            reference = subprocess.run(
                [sys.executable, "-I", "-c", CPYTHON, str(python_file), json.dumps(names), json.dumps(seeds)],
                check=True, capture_output=True, text=True, timeout=10,
            )
            actual_completion, actual = json.loads(reference.stdout)
            assert (actual_completion, actual) == (completion, namespace), (name, reference.stdout)
            assert all(type(actual[key]) is type(value) for key, value in namespace.items()), (name, actual)
            bindings = ", ".join(f"({json.dumps(key)}, {lean_value(value)})" for key, value in seeds.items())
            values = ", ".join("none" if value is None else "some (" + lean_value(value) + ")"
                               for value in namespace.values())
            result = f"some ({observed}, [{values}], {events})"
            test = f"\n#guard observation pythonSource [{bindings}] {json.dumps(names)} == {result}\n"
            if name == "seed_and_overwrite":
                test += "#print axioms Compiled.finishes_iff\n#print axioms Compiled.run_finishes\n"
            fixtures.append((source, test))
            observations[name] = {"completion": completion, "globals": namespace, "visible_core_labels": events}
        fixtures.extend((source, "#guard unsupportedIndex pythonSource") for source in UNSUPPORTED_INDEXING)
        fixtures.extend((source, f"#guard rejection pythonSource == some ({error})")
                        for source, error in REJECTED_BRANCHES)
        fixtures.extend(boolean_rejection_fixtures())
        fixtures.extend(sequence_rejection_fixtures())
        shared["check_lean_batch"](Path(tmp) / "Example.py", Path(tmp) / "Fixtures.lean",
                                   fixtures, LEAN, extra_imports=imports)
    print(json.dumps({"cpython": sys.version.split()[0], "observations": observations}))
