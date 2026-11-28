# SPDX-License-Identifier: MIT
"""Check compiled module calls and residual bindings against CPython."""

import json
import re
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile


FIXTURES = (
    ("closed_positional_addition", """def identity(value):
    return value
observed = identity(1 + 2)
""", "normal", ".normal", 3, None),
    ("persistent_dictionary_alias", """d = {True: 2, 1: 7}
alias = d
d = {1: 9}
observed = alias.get(1)
kept = d.get(True)
""", "normal", ".normal", 7, 9),
    ("persistent_dictionary_clear", """d = {1: 7}
alias = d
other = {1: 9}
result = d.clear()
observed = alias.get(1, 0)
kept = other.get(1)
""", "normal", ".normal", 0, 9),
    ("dictionary_argument_to_closure", """def identity(value):
    return value
d = identity({True: 2, 1: 7})
observed = d.get(1)
""", "normal", ".normal", 7, None),
    ("none_literal_preserved", """observed = None
assert observed == None
assert observed != False
assert not observed
kept = 4
""", "normal", ".normal", None, 4),
    ("none_literal_left_lookup", """observed = None
observed = missing_first != missing_second
kept = 4
""", "NameError", '.raised (.nameError "missing_first")', None, None),
    ("none_literal_arithmetic_profile", """observed = None
kept = 7
observed = observed + 1
kept = 9
""", "TypeError", ".scalarProfile", None, 7),
    ("adjacent_keyword_discard", """kept = 5
def probe(value):
    assert False
def probe(value):
    assert value == 4
probe(**{"value": 4})
observed = 9
""", "normal", ".normal", 9, 5),
    ("adjacent_keyword_failure", """kept = 5
def probe(value):
    assert value == 4
probe(**{"value": 3})
observed = 9
""", "AssertionError", ".raised .assertionError", None, 5),
    ("literal_if_selected_order", """kept = 1
if True:
    kept = 4
    observed = kept
else:
    assert missing
if 0:
    observed = 9
else:
    assert observed == 4
""", "normal", ".normal", 4, 4),
    ("literal_if_selected_failure", """kept = 1
if False:
    assert missing
else:
    kept = 4
    assert False
    kept = 9
observed = 8
""", "AssertionError", ".assertionError", None, 4),
    ("literal_conditional_selected", """kept = 1
observed = missing if False else kept
assert False if 0 else True
""", "normal", ".normal", 1, 1),
    ("literal_conditional_selected_error", """kept = 4
observed = 7
observed = selected_missing if True else ignored_missing
kept = 9
""", "NameError", '.raised (.nameError "selected_missing")', 7, 4),
    ("body_code_names_live_rebind", """global_x = 1
def first():
    assert global_x == 1
def empty():
    pass
def probe():
    assert "global_x" in target.__code__.co_names
def through_alias():
    assert "global_x" in saved.__code__.co_names
    return 7
target = first
saved = target
probe()
target = empty
observed = through_alias()
observed = probe()
kept = 9
""", "AssertionError", ".raised .assertionError", 7, None),
    ("body_cellvars_global", """def target():
    pass
def inspect():
    assert "unused" not in target.__code__.co_cellvars
    return 4
observed = inspect()
""", "normal", ".normal", 4, None),
    ("body_cellvars_nonmembership_failure", """def target():
    zeta = 4
    def leaf():
        return zeta
    leaf()
def inspect():
    assert "zeta" not in target.__code__.co_cellvars
    return 9
observed = 5
observed = inspect()
kept = 9
""", "AssertionError", ".raised .assertionError", 5, None),
    ("body_freevars_global", """def target():
    pass
def inspect():
    assert "unused" not in target.__code__.co_freevars
    return 4
observed = inspect()
""", "normal", ".normal", 4, None),
    ("body_freevars_membership_failure", """def target():
    pass
def inspect():
    assert "unused" in target.__code__.co_freevars
    return 9
observed = 5
observed = inspect()
kept = 9
""", "AssertionError", ".raised .assertionError", 5, None),
    ("body_discard_call_current_global", """def target():
    assert False
def caller():
    target()
    return 5
def target():
    return 3
observed = caller()
""", "normal", ".normal", 5, None),
    ("body_discard_call_missing_global", """def caller():
    missing()
    return 9
observed = 5
observed = caller()
kept = 9
""", "NameError", '.raised (.nameError "missing")', 5, None),
    ("body_assert_bool_failure", """def guarded():
    assert False
    return 0
observed = 5
observed = guarded()
kept = 9
""", "AssertionError", ".raised .assertionError", 5, None),
    ("body_assert_delivery", """def guarded(value):
    assert value
    return value
observed = 5
kept = 4
assert guarded(0)
kept = 9
""", "AssertionError", ".raised .assertionError", 5, 4),
    ("body_assert_operand_error", """def guarded():
    assert absent
    return 0
observed = 5
observed = guarded()
kept = 9
""", "NameError", '.raised (.nameError "absent")', 5, None),
    ("body_assert_eq_int_globals", """value = 1
def guarded():
    global value
    assert value == 2
    return value
value = 2
observed = guarded()
""", "normal", ".normal", 2, None),
    ("body_assert_eq_int_missing_global", """def guarded():
    assert absent == 0
    return 9
observed = 5
observed = guarded()
kept = 9
""", "NameError", '.raised (.nameError "absent")', 5, None),
    ("body_assert_eq_int_bool", """def guarded(value):
    assert value == 1
    return 9
def check_zero(value):
    assert value == 0
    return 4
yes = True
no = False
observed = guarded(yes)
kept = check_zero(no)
observed = guarded(no)
kept = 9
""", "AssertionError", ".raised .assertionError", 9, 4),
    ("body_assert_eq_int_none", """def quiet():
    pass
def guarded(value):
    assert value == 0
    return 9
value = quiet()
observed = 5
observed = guarded(value)
kept = 9
""", "AssertionError", ".raised .assertionError", 5, None),
    ("body_assert_eq_int_function", """def guarded(value):
    assert value == 0
    return 9
observed = 5
observed = guarded(guarded)
kept = 9
""", "AssertionError", ".raised .assertionError", 5, None),
    ("rebind", """value = 1
def read():
    return value
def shadow(value):
    return value
value = 2
observed = read()
kept = shadow(3)
read()
""", "normal", ".normal", 2, 3),
    ("addition_slots", """base = 100
bias = 5
def factory(base):
    def wrapper():
        def add(n):
            return (base + n) + bias
        return add
    base = base + 1
    return wrapper()
saved = factory(3)
bias = 8
observed = saved(2)
yes = True
kept = saved(yes)
""", "normal", ".normal", 14, 13),
    ("addition_left_read_error", """def add():
    return missing_left + missing_right
observed = 5
observed = add()
kept = 9
""", "NameError", '.raised (.nameError "missing_left")', 5, None),
    ("addition_right_read_before_type_error", """def add():
    return add + missing_right
observed = 5
observed = add()
kept = 9
""", "NameError", '.raised (.nameError "missing_right")', 5, None),
    ("addition_type_error", """def add():
    return add + 1
observed = 5
observed = add()
kept = 9
""", "TypeError", ".raised .additionTypeError", 5, None),
    ("missing", """def read():
    global absent
    return absent
observed = 5
observed = read()
""", "NameError", '.raised (.nameError "absent")', 5, None),
    ("arity", """def identity(value):
    return value
observed = 5
observed = identity()
""", "TypeError", ".raised (.positionalArity 1 0)", 5, None),
    ("not_callable", """target = 1
observed = 5
observed = target()
""", "TypeError", ".raised .notCallable", 5, None),
    ("assert_call", """def identity(value):
    return value
assert identity(1)
kept = 4
assert identity(0)
observed = 2
""", "AssertionError", ".assertionError", None, 4),
    ("function_pass", """def identity(value):
    pass
    answer = value
    pass
    return answer
observed = identity(6)
""", "normal", ".normal", 6, None),
    ("implicit_none_binding", """def quiet():
    pass
observed = quiet()
kept = 4
assert quiet()
kept = 9
""", "AssertionError", ".assertionError", None, 4),
    ("negated_scalar", """assert not (7 == 8)
assert not 0
observed = 42
assert not 1
kept = 9
""", "AssertionError", ".assertionError", 42, None),
    ("negated_none", """def quiet():
    pass
observed = quiet()
assert not observed
kept = 4
""", "normal", ".normal", None, 4),
    ("negated_lookup_order", """observed = 5
assert not (missing_left == missing_right)
kept = 9
""", "NameError", '.raised (.nameError "missing_left")', 5, None),
    ("negated_division_error", """kept = 5
assert not (1 // 0)
observed = 3
""", "ZeroDivisionError", ".raised (.arithmetic .zeroDivisionError)", None, 5),
    ("nested_assignment", """def identity(value):
    return value
def select(first, second, third):
    return third
value = 7
observed = select(identity(1), value, identity(42))
identity(identity(3))
assert identity(identity(1))
""", "normal", ".normal", 42, None),
    ("nested_lookup_order", """observed = 5
observed = missing_outer(missing_inner())
kept = 8
""", "NameError", '.raised (.nameError "missing_outer")', 5, None),
    ("nested_argument_order", """def identity(value):
    return value
def select(first, second):
    return second
observed = 5
observed = select(identity(missing_first), missing_second())
kept = 8
""", "NameError", '.raised (.nameError "missing_first")', 5, None),
    ("nested_noncallable_order", """target = 0
observed = 5
observed = target(missing_inner())
kept = 8
""", "NameError", '.raised (.nameError "missing_inner")', 5, None),
    ("nested_arity", """def identity(value):
    return value
observed = 5
observed = identity(identity())
kept = 8
""", "TypeError", ".raised (.positionalArity 1 0)", 5, None),
    ("nested_assertion", """def identity(value):
    return value
kept = 5
assert identity(identity(0))
observed = 9
""", "AssertionError", ".assertionError", None, 5),
)

LEAN = """
open Silmaril.Languages.Python
open Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run

private def readInt (session : Core.Module.Functions.Session) (name : String) : Option Int :=
  match session.globals name with
  | some (.int value) => some value
  | _ => none

private def noneBound (session : Core.Module.Functions.Session) (name : String) : Bool :=
  match session.globals name with
  | some .none => true
  | _ => false

private def observe (source : Module) : Option (Completion × Option Int × Option Int × Bool) := do
  let compiled ← (compile source).toOption
  let (_, live) := runPrefix compiled.table 5 compiled.start
  match (runPrefix compiled.table 128 live).2 with
  | .finished session result =>
    some (result, readInt session "observed", readInt session "kept", noneBound session "observed")
  | _ => none
"""

NESTED_TRACE = """
private def enteredKeys (events : List Core.Closure.Executor.Event) : List Nat :=
  events.filterMap fun
    | .enter (.function function) => some function.code.key
    | _ => none

#guard (match compile pythonSource with
  | .ok compiled =>
    let (first, paused) := runPrefix compiled.table 6 compiled.start
    match paused with
    | .calling .. =>
      let (rest, _) := runPrefix compiled.table 128 paused
      enteredKeys first == [0] && enteredKeys rest == [0, 1, 0, 0, 0, 0]
    | _ => false
  | _ => false)
"""

CPYTHON = """
import json
import sys

namespace = {"__builtins__": {}}
completion = "normal"
missing = None
try:
    with open(sys.argv[1], encoding="utf-8") as source:
        exec(compile(source.read(), sys.argv[1], "exec", dont_inherit=True, optimize=0), namespace)
except (AssertionError, NameError, TypeError, ZeroDivisionError) as error:
    completion = type(error).__name__
    if isinstance(error, AssertionError):
        assert not error.args
    if isinstance(error, NameError):
        missing = error.name
bound_none = "observed" in namespace and namespace["observed"] is None
print(json.dumps([completion, missing, namespace.get("observed"), namespace.get("kept"), bound_none]))
"""


def optional(value):
    return "none" if value is None else f"some {value}"


if __name__ == "__main__":
    shared = runpy.run_path(str(Path(__file__).resolve().parent.parent / "source-scope/check_intake.py"))
    imports = (
        "import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Thms",
        "meta import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Defs",
        "meta import Silmaril.Languages.Python.Core.Module.Functions.Defs",
        "meta import Silmaril.Languages.Python.Core.Closure.Defs",
        "meta import Silmaril.Languages.Python.Core.Closure.Executor.Defs",
    )
    observations = {}
    fixtures = []
    with tempfile.TemporaryDirectory() as tmp:
        source_file = Path(tmp) / "Example.py"
        lean_file = Path(tmp) / "Example.lean"
        for name, source, completion, lean, observed, kept in FIXTURES:
            source_file.write_text(source, encoding="utf-8")
            result = subprocess.run(
                [sys.executable, "-I", "-c", CPYTHON, str(source_file)],
                text=True, capture_output=True, check=True, timeout=10,
            )
            name_error = re.fullmatch(r'\.raised \(\.nameError "([^"]+)"\)', lean)
            missing = name_error.group(1) if name_error else None
            bound_none = name in {"implicit_none_binding", "negated_none",
                                  "none_literal_preserved", "none_literal_left_lookup",
                                  "none_literal_arithmetic_profile"}
            assert json.loads(result.stdout) == [completion, missing, observed, kept, bound_none], (name, result.stdout)
            assert result.stderr == "", (name, result.stderr)
            test = f"\n#guard observe pythonSource == some ({lean}, {optional(observed)}, {optional(kept)}, {json.dumps(bound_none)})\n"
            if name == "rebind":
                test += "#print axioms seed_lookup\n#print axioms invoke_current_globals\n#print axioms runPrefix_append\n"
            if name == "nested_assignment":
                test += NESTED_TRACE
            fixtures.append((source, test))
            observations[name] = {"completion": completion, "observed": observed, "kept": kept, "bound_none": bound_none}
        fixtures.append(("def identity(x): return x\nidentity(missing + 2)\n", """
#guard (match compile pythonSource with | .error .callOperand => true | _ => false)
"""))
        for source in (
            'def probe(value): pass\nprobe(**{"other": 4})',
            'def probe(é): pass\nprobe(**{"e\u0301": 4})',
            'def probe(value): pass\nother(**{"value": 4})',
            'def probe(value): pass\npass\nprobe(**{"value": 4})',
            'def probe(value): pass\nprobe(**{"value": 4, "other": 1})',
            'def probe(value): pass\nprobe(**{"value": 2 + 2})',
            'def probe(value): pass\nprobe(value=4)',
            'def probe(value): pass\nresult = probe(**{"value": 4})',
        ):
            fixtures.append((source + "\n", """
#guard (match compile pythonSource with | .error (.source .argumentProfile) => true | _ => false)
"""))
        for source, error in (
            ("assert not f()", ".source (.scalar .expressionProfile)"),
            ("assert not (left is right)", ".source (.scalar .expressionProfile)"),
            ('assert not 0, "message"', ".source (.scalar .assertionMessage)"),
            ("outer(inner(child(1)))", ".source (.scalar .expressionProfile)"),
            ("outer(inner(value=1))", ".source (.scalar .expressionProfile)"),
            ("outer(inner(*values))", ".source (.scalar .expressionProfile)"),
            ("outer(inner(missing + 2))", ".callOperand"),
        ):
            fixtures.append((source + "\n", f"""
#guard (match compile pythonSource with | .error ({error}) => true | _ => false)
"""))
        shared["check_lean_batch"](source_file, lean_file, fixtures, LEAN, extra_imports=imports)
    print(json.dumps({"cpython": sys.version.split()[0], "observations": observations}))
