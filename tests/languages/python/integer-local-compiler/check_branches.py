# SPDX-License-Identifier: MIT
"""Replay original integer branch fixtures through CPython and Lean."""

import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile


FIXTURES = (
    ("short_circuit", """def answer():
    if (0 or 0 or 5) and 1:
        y = 41
        return y + (1 or 1 // 0)
    else:
        return 1 // 0
""", "return 42"),
    ("lazy_false", """def answer():
    if 0 and 1 // 0:
        return 1 // 0
    else:
        return 7
""", "return 7"),
    ("division_in_test", """def answer():
    if 1 // 0:
        return 1
    else:
        return 2
""", "ZeroDivisionError"),
    ("unbound_in_test", """def answer():
    if x:
        x = 1
        return x
    else:
        return 2
""", "UnboundLocalError"),
)

CPYTHON = """
import runpy
import sys

try:
    print("return", runpy.run_path(sys.argv[1])["answer"]())
except (ZeroDivisionError, UnboundLocalError) as error:
    print(type(error).__name__)
"""

LEAN = """
open Silmaril.Languages.Python
open Silmaril.Languages.Python.Compile.Locals

private def observation (source : Module) : String :=
  match compile source with
  | .error _ => "compile error"
  | .ok compiled =>
    match Core.Locals.run compiled.code compiled.code.budget with
    | .stop (.finished _ (.ok value)) (.observed (.returned (.ok observed))) =>
      if value == observed then s!"return {value}" else "inconsistent observation"
    | .stop (.finished _ (.error (.arithmetic .zeroDivisionError))) (.observed (.returned (.error _))) =>
      "ZeroDivisionError"
    | .stop (.finished _ (.error (.unboundLocal _))) (.observed (.returned (.error _))) =>
      "UnboundLocalError"
    | _ => "unexpected runner result"
"""


if __name__ == "__main__":
    shared = runpy.run_path(str(Path(__file__).resolve().parent.parent / "source-scope/check_intake.py"))
    imports = (
        "import Silmaril.Languages.Python.Compile.Locals.Thms",
        "meta import Silmaril.Languages.Python.Compile.Locals.Defs",
        "meta import Silmaril.Languages.Python.Core.Locals.Thms",
    )
    outcomes = {}
    with tempfile.TemporaryDirectory() as tmp:
        for name, source, expected in FIXTURES:
            python_file = Path(tmp) / f"{name}.py"
            lean_file = Path(tmp) / "Fixture.lean"
            shared["emit"](python_file, lean_file, source)
            reference = subprocess.run(
                [sys.executable, "-I", "-c", CPYTHON, str(python_file)],
                check=True, capture_output=True, text=True, timeout=10,
            ).stdout.strip()
            assert reference == expected, (name, reference, expected)
            shared["check_lean"](
                lean_file, LEAN + f"\n#guard observation pythonSource == {json.dumps(expected)}\n",
                extra_imports=imports, capture_output=True,
            )
            outcomes[name] = reference
    print(json.dumps({"cpython": sys.version.split()[0], "observations": outcomes}))
