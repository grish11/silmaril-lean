# SPDX-License-Identifier: MIT
"""Compare original fixed-positional Python closure fixtures with Core."""

import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile


FIXTURES = (
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
except NameError:
    print("NameError")
"""

LEAN = """
open Silmaril.Languages.Python
open Silmaril.Languages.Python.Compile.Closure.Run

private def resultName : Core.Closure.Result → String
  | .ok (.int value) => s!"return {value}"
  | .error (.positionalArity 1 0) => "TypeError arity"
  | .error .notCallable => "TypeError noncallable"
  | .error (.unboundCapture _) => "NameError"
  | _ => "unexpected result"

private def eventName : Core.Closure.Executor.Event → String
  | .enter _ => "enter"
  | .resume _ => "resume"
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
    with tempfile.TemporaryDirectory() as tmp:
        for name, source, expected, events in FIXTURES:
            python_file = Path(tmp) / f"{name}.py"
            lean_file = Path(tmp) / "Fixture.lean"
            shared["emit"](python_file, lean_file, source)
            reference = subprocess.run(
                [sys.executable, "-I", "-c", CPYTHON, str(python_file)],
                check=True, capture_output=True, text=True, timeout=10,
            ).stdout.strip()
            assert reference == expected, (name, reference, expected)
            extra = ""
            if name == "forwarded_write":
                extra = '#guard observation pythonSource 1 == ("live residual", [])\n'
            shared["check_lean"](
                lean_file,
                LEAN + f"\n#guard observation pythonSource 64 == ({json.dumps(expected)}, {json.dumps(events)})\n" + extra,
                extra_imports=imports, capture_output=True,
            )
            observations[name] = {"result": reference, "core_events": events}

        shared["emit"](python_file, lean_file, "def outer(seed): return seed + 1\n")
        shared["check_lean"](
            lean_file,
            LEAN + """
#guard (match compile pythonSource with | .error (.bodyProfile [0]) => true | _ => false)
""",
            extra_imports=imports, capture_output=True,
        )
    print(json.dumps({"cpython": sys.version.split()[0], "observations": observations, "fuel_budget": 64}))
