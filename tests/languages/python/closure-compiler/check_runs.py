# SPDX-License-Identifier: MIT
"""Compare original fixed-positional Python closure fixtures with Core."""

import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile


FIXTURES = (
    ("sum_parameter", """def outer(seed):
    return seed + 1
""", "return 6", ["complete"]),
    ("assert_sum", """def outer(seed):
    assert seed + 1
    return seed
""", "return 5", ["complete"]),
    ("pass", """def outer(seed):
    pass
    return seed
""", "return 5", ["complete"]),
    ("nested_pass", """def outer(seed):
    pass
    def inner(value):
        pass
        return value
    pass
    result = inner(seed)
    pass
    return result
""", "return 5", ["enter", "resume", "complete"]),
    ("implicit_none", """def outer(seed):
    pass
""", "return None", ["complete None"]),
    ("nested_implicit_none", """def outer(seed):
    def inner(value):
        copy = value
    result = seed
    result = inner(seed)
    return result
""", "return None", ["enter", "resume None", "complete None"]),
    ("body_discard_call_paths", """def outer(seed):
    def write():
        nonlocal seed
        seed = 41
        return 99
    keep = 7
    write()
    assert keep == 7
    def read():
        return seed
    result = read()
    return result
""", "return 41", ["enter", "resume", "enter", "resume", "complete"]),
    ("body_discard_call_error", """def outer(seed):
    def child():
        nonlocal seed
        seed = 41
        assert False
        return seed
    child()
    seed = 99
    return seed
""", "AssertionError", ["enter", "resume AssertionError", "complete AssertionError"]),
    ("body_discard_call_noncallable", """def outer(seed):
    seed()
    return seed
""", "TypeError noncallable", ["complete"]),
    ("body_assert_child_path", """def outer(seed):
    assert seed
    def child(value):
        assert value
        return value
    result = child(seed)
    return result
""", "return 5", ["enter", "resume", "complete"]),
    ("body_assert_saved_caller", """def outer(seed):
    def quiet():
        pass
    def child(value):
        nonlocal seed
        seed = 41
        assert value
        seed = 99
        return seed
    value = quiet()
    result = child(value)
    return result
""", "AssertionError", ["enter", "resume None", "enter", "resume AssertionError", "complete AssertionError"]),
    ("body_assert_bool_paths", """def outer(seed):
    assert True
    def first(value):
        assert True
        return value
    assert True
    def second(value):
        return value
    middle = first(seed)
    result = second(middle)
    return result
""", "return 5", ["enter", "resume", "enter", "resume", "complete"]),
    ("body_assert_bool_false", """def outer(seed):
    def child():
        nonlocal seed
        seed = 41
        assert False
        seed = 99
        return seed
    result = child()
    return result
""", "AssertionError", ["enter", "resume AssertionError", "complete AssertionError"]),
    ("body_assert_eq_int_paths", """def outer(seed):
    assert seed == 5
    def first():
        assert seed == 5
        return seed
    assert seed == 5
    def second(value):
        assert value == 5
        return value
    middle = first()
    result = second(middle)
    return result
""", "return 5", ["enter", "resume", "enter", "resume", "complete"]),
    ("body_assert_eq_int_saved_caller", """def outer(seed):
    def child():
        nonlocal seed
        seed = 41
        assert seed == 5
        seed = 99
        return seed
    result = child()
    return result
""", "AssertionError", ["enter", "resume AssertionError", "complete AssertionError"]),
    ("body_assert_eq_int_unbound_local", """def outer(seed):
    assert hidden == 5
    hidden = seed
    return hidden
""", "UnboundLocalError", ["complete"]),
    ("body_assert_eq_int_unbound_capture", """def outer(seed):
    def child():
        assert hidden == 5
        return seed
    result = child()
    hidden = seed
    return result
""", "NameError", ["enter", "resume", "complete"]),
    ("forwarded_write", """def outer(seed):
    def middle(x):
        def inner(y):
            nonlocal seed
            seed = y
            return seed
        answer = inner(x)
        return answer
    result = middle(42)
    return seed
""", "return 42", ["enter", "enter", "resume", "resume", "complete"]),
    ("wrong_arity", """def outer(seed):
    def inner(x):
        return seed
    result = inner()
    return result
""", "TypeError arity", ["complete"]),
    ("noncallable", """def outer(seed):
    result = seed()
    return result
""", "TypeError noncallable", ["complete"]),
    ("unbound_capture", """def outer(seed):
    def inner():
        return hidden
    result = inner()
    hidden = seed
    return result
""", "NameError", ["enter", "resume", "complete"]),
)

CPYTHON = """
import runpy
import sys

try:
    print("return", runpy.run_path(sys.argv[1])["outer"](5))
except TypeError as error:
    if "required positional argument" in str(error):
        print("TypeError arity")
    elif "not callable" in str(error):
        print("TypeError noncallable")
    else:
        raise
except UnboundLocalError:
    print("UnboundLocalError")
except NameError:
    print("NameError")
except AssertionError as error:
    assert not error.args
    print("AssertionError")
"""

LEAN = """
open Silmaril.Languages.Python
open Silmaril.Languages.Python.Compile.Closure.Run

private def resultName : Core.Closure.Result → String
  | .ok .none => "return None"
  | .ok (.int value) => s!"return {value}"
  | .error (.positionalArity 1 0) => "TypeError arity"
  | .error .notCallable => "TypeError noncallable"
  | .error (.unboundLocal _) => "UnboundLocalError"
  | .error (.unboundCapture _) => "NameError"
  | .error .assertionError => "AssertionError"
  | _ => "unexpected result"

private def eventName : Core.Closure.Executor.Event → String
  | .enter _ => "enter"
  | .resume (.ok .none) => "resume None"
  | .resume (.error .assertionError) => "resume AssertionError"
  | .resume _ => "resume"
  | .complete (.ok .none) => "complete None"
  | .complete (.error .assertionError) => "complete AssertionError"
  | .complete _ => "complete"
  | .fault _ => "fault"

private def observation (source : Module) (fuel : Nat) : String × List String :=
  match compile source with
  | .error _ => ("compile error", [])
  | .ok compiled =>
    match run compiled [.int 5] fuel with
    | .error _ => ("entry error", [])
    | .ok (events, residual) =>
      let status := match residual with
        | .finished _ result => resultName result
        | .faulted .. => "invalid runtime reference"
        | _ => "live residual"
      (status, events.map eventName)

private def retainedAssertionWrite (source : Module) : Bool :=
  match compile source with
  | .ok compiled => match run compiled [.int 5] 64 with
    | .ok (_, .finished heap (.error .assertionError)) =>
      match heap.lookup ⟨0⟩ with
      | some (some (.int 41)) => true
      | _ => false
    | _ => false
  | .error _ => false

"""


if __name__ == "__main__":
    shared = runpy.run_path(str(Path(__file__).resolve().parent.parent / "source-scope/check_intake.py"))
    imports = (
        "import Silmaril.Languages.Python.Compile.Closure.Run.Thms",
        "meta import Silmaril.Languages.Python.Compile.Closure.Run.Defs",
        "meta import Silmaril.Languages.Python.Core.Closure.Executor.Defs",
        "meta import Silmaril.Languages.Python.Core.Closure.Defs",
    )
    observations = {}
    fixtures = []
    with tempfile.TemporaryDirectory() as tmp:
        for name, source, expected, events in FIXTURES:
            python_file = Path(tmp) / f"{name}.py"
            python_file.write_text(source, encoding="utf-8")
            reference = subprocess.run(
                [sys.executable, "-I", "-c", CPYTHON, str(python_file)],
                check=True, capture_output=True, text=True, timeout=10,
            ).stdout.strip()
            assert reference == expected, (name, reference, expected)
            extra = ""
            if name == "pass":
                extra = '#guard observation pythonSource 2 == ("return 5", ["complete"])\n'
            elif name == "implicit_none":
                extra = '#guard observation pythonSource 2 == ("return None", ["complete None"])\n'
            elif name == "body_discard_call_paths":
                extra = """
#guard (match compile pythonSource with
  | .ok compiled =>
    compiled.sourceBody.paths == [[0], [0, 0], [0, 1]] &&
      match compiled.table compiled.entry.key with
      | some entry => match entry.definition.body with
        | .store _ _ (.store _ _ (.callTo .discard (.read _) [] _)) => true
        | _ => false
      | none => false
  | .error _ => false)
"""
            elif name == "body_discard_call_error":
                extra = "#guard retainedAssertionWrite pythonSource\n"
            elif name == "body_assert_child_path":
                extra = """
#guard (match compile pythonSource with
  | .ok compiled => compiled.sourceBody.paths == [[0], [0, 0]]
  | .error _ => false)
"""
            elif name == "body_assert_bool_paths":
                extra = """
#guard (match compile pythonSource with
  | .ok compiled =>
    compiled.sourceBody.paths == [[0], [0, 0], [0, 1]] &&
      match compiled.table compiled.entry.key with
      | some entry => match entry.definition.body with
        | .assert (.literal (.bool true)) _ => true
        | _ => false
      | none => false
  | .error _ => false)
"""
            elif name == "body_assert_bool_false":
                extra = """
#guard retainedAssertionWrite pythonSource
#guard (match compile pythonSource with
  | .ok compiled => match compiled.table 1 with
    | some entry => match entry.definition.body with
      | .store _ _ (.assert (.literal (.bool false)) _) => true
      | _ => false
    | none => false
  | .error _ => false)
"""
            elif name == "body_assert_saved_caller":
                extra = "#guard retainedAssertionWrite pythonSource\n"
            elif name == "body_assert_eq_int_paths":
                extra = """
#guard (match compile pythonSource with
  | .ok compiled =>
    compiled.sourceBody.paths == [[0], [0, 0], [0, 1]] &&
      match compiled.table compiled.entry.key, compiled.table 1 with
      | some outer, some inner => match outer.definition.body, inner.definition.body with
        | .assert (.eqInt (.slot (.owned _)) 5) _, .assert (.eqInt (.slot (.capture _)) 5) _ => true
        | _, _ => false
      | _, _ => false
  | .error _ => false)
"""
            elif name == "body_assert_eq_int_saved_caller":
                extra = "#guard retainedAssertionWrite pythonSource\n"
            elif name == "forwarded_write":
                extra = '#guard observation pythonSource 1 == ("live residual", [])\n'
            check = f"\n#guard observation pythonSource 64 == ({json.dumps(expected)}, {json.dumps(events)})\n"
            fixtures.append((source, check + extra))
            observations[name] = {"result": reference, "core_events": events}

        source = "def outer(seed): return\n"
        python_file = Path(tmp) / "BareReturn.py"
        python_file.write_text(source, encoding="utf-8")
        bare_return = subprocess.run(
            [sys.executable, "-I", "-c", CPYTHON, str(python_file)],
            check=True, capture_output=True, text=True, timeout=10,
        )
        assert bare_return.stdout.strip() == "return None"
        fixtures.append((source, """
#guard (match compile pythonSource with | .error (.frontend .bodyShape) => true | _ => false)
"""))
        for source, diagnostic in (
            ('def outer(seed): assert "x" not in seed().__code__.co_cellvars', ".frontend .expressionShape"),
            ('def outer(seed): assert "x" not in seed.__code__.co_cellvars, "message"', ".frontend .bodyShape"),
            ('def outer(seed): assert "x" in seed.__code__.co_cellvars', ".frontend .expressionShape"),
            ('def outer(seed): assert "x" in seed().__code__.co_names', ".frontend .expressionShape"),
            ('def outer(seed): assert "x" not in seed.__code__.co_names', ".frontend .expressionShape"),
            ('def outer(seed): assert "x" in seed.__code__.co_names, "message"', ".frontend .bodyShape"),
            ('def outer(seed): assert "x" in seed().__code__.co_freevars', ".frontend .expressionShape"),
            ('def outer(seed): assert "x" in seed.__code__.co_freevars, "message"', ".frontend .bodyShape"),
            ("def outer(seed): seed(5)", ".frontend .bodyShape"),
            ("def outer(seed): seed(value=5)", ".frontend .bodyShape"),
            ("def outer(seed): seed(*())", ".frontend .bodyShape"),
            ('def outer(seed): seed(**{})', ".frontend .bodyShape"),
            ("def outer(seed): seed.attribute()", ".frontend .bodyShape"),
            ("def outer(seed): seed()()", ".frontend .bodyShape"),
            ("def outer(seed): assert seed()", ".bodyProfile [0]"),
            ("def outer(seed): assert seed == True", ".frontend .expressionShape"),
            ("def outer(seed): assert seed == 5 == seed", ".frontend .expressionShape"),
            ("def outer(seed): assert seed() == 5", ".frontend .expressionShape"),
            ("def outer(seed): assert seed != 5", ".frontend .expressionShape"),
            ("def outer(seed): return seed == 5", ".frontend .expressionShape"),
            ("def outer(seed): assert True and False", ".frontend .expressionShape"),
            ("def outer(seed): assert seed == 5 and seed", ".frontend .expressionShape"),
            ("def outer(seed): return True", ".frontend .expressionShape"),
            ('def outer(seed): assert False, "message"', ".frontend .bodyShape"),
            ('def outer(seed): assert seed == 5, "message"', ".frontend .bodyShape"),
        ):
            fixtures.append((source + "\n", f"""
#guard (match compile pythonSource with | .error ({diagnostic}) => true | _ => false)
"""))
        shared["check_lean_batch"](Path(tmp) / "Example.py", Path(tmp) / "Fixtures.lean",
                                   fixtures, LEAN, extra_imports=imports)
    print(json.dumps({"cpython": sys.version.split()[0], "observations": observations, "fuel_budget": 64}))
