# SPDX-License-Identifier: MIT
"""Check compiled module calls and residual bindings against CPython."""

import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile


FIXTURES = (
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
)

LEAN = """
open Silmaril.Languages.Python
open Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run

private def readInt (session : Core.Module.Functions.Session) (name : String) : Option Int :=
  match session.globals name with
  | some (.int value) => some value
  | _ => none

private def observe (source : Module) : Option (Completion × Option Int × Option Int) := do
  let compiled ← (compile source).toOption
  let (_, live) := runPrefix compiled.table 5 compiled.start
  match (runPrefix compiled.table 128 live).2 with
  | .finished session result => some (result, readInt session "observed", readInt session "kept")
  | _ => none
"""

CPYTHON = """
import json
import sys

namespace = {"__builtins__": {}}
completion = "normal"
try:
    with open(sys.argv[1], encoding="utf-8") as source:
        exec(compile(source.read(), sys.argv[1], "exec", optimize=0), namespace)
except (NameError, TypeError) as error:
    completion = type(error).__name__
print(json.dumps([completion, namespace.get("observed"), namespace.get("kept")]))
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
    )
    observations = {}
    with tempfile.TemporaryDirectory() as tmp:
        source_file = Path(tmp) / "Example.py"
        lean_file = Path(tmp) / "Example.lean"
        for name, source, completion, lean, observed, kept in FIXTURES:
            shared["emit"](source_file, lean_file, source)
            result = subprocess.run(
                [sys.executable, "-I", "-c", CPYTHON, str(source_file)],
                text=True, capture_output=True, check=True, timeout=10,
            )
            assert json.loads(result.stdout) == [completion, observed, kept], (name, result.stdout)
            test = f"\n#guard observe pythonSource == some ({lean}, {optional(observed)}, {optional(kept)})\n"
            if name == "rebind":
                test += "#print axioms seed_lookup\n#print axioms invoke_current_globals\n#print axioms runPrefix_append\n"
            shared["check_lean"](lean_file, LEAN + test, extra_imports=imports)
            observations[name] = {"completion": completion, "observed": observed, "kept": kept}
        shared["emit"](source_file, lean_file, "def identity(x): return x\nidentity(1 + 2)\n")
        shared["check_lean"](lean_file, LEAN + """
#guard (match compile pythonSource with | .error .callOperand => true | _ => false)
""", extra_imports=imports)
    print(json.dumps({"cpython": sys.version.split()[0], "observations": observations}))
