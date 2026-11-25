# SPDX-License-Identifier: MIT
"""Compare actual Python modules with source lowering and the Core runner."""

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
"""


def lean_value(value):
    if isinstance(value, bool):
        return ".bool true" if value else ".bool false"
    assert isinstance(value, int), value
    return f".int ({value})"


if __name__ == "__main__":
    shared = runpy.run_path(str(Path(__file__).resolve().parent.parent / "source-scope/check_intake.py"))
    imports = (
        "import Silmaril.Languages.Python.Compile.ModuleEntry.Run.Thms",
        "meta import Silmaril.Languages.Python.Compile.ModuleEntry.Run.Defs",
        "meta import Silmaril.Languages.Python.Core.Module.Defs",
    )
    observations = {}
    with tempfile.TemporaryDirectory() as tmp:
        for name, source, seeds, namespace, completion, observed, events in FIXTURES:
            python_file = Path(tmp) / f"{name}.py"
            lean_file = Path(tmp) / "Fixture.lean"
            shared["emit"](python_file, lean_file, source)
            names = list(namespace)
            reference = subprocess.run(
                [sys.executable, "-I", "-c", CPYTHON, str(python_file), json.dumps(names), json.dumps(seeds)],
                check=True, capture_output=True, text=True, timeout=10,
            )
            assert json.loads(reference.stdout) == [completion, namespace], (name, reference.stdout)
            bindings = ", ".join(f"({json.dumps(key)}, {lean_value(value)})" for key, value in seeds.items())
            values = ", ".join("none" if value is None else "some (" + lean_value(value) + ")"
                               for value in namespace.values())
            result = f"some ({observed}, [{values}], {events})"
            test = f"\n#guard observation pythonSource [{bindings}] {json.dumps(names)} == {result}\n"
            if name == "seed_and_overwrite":
                test += "#print axioms Compiled.finishes_iff\n#print axioms Compiled.run_finishes\n"
            shared["check_lean"](lean_file, LEAN + test, extra_imports=imports)
            observations[name] = {"completion": completion, "globals": namespace, "visible_core_labels": events}
    print(json.dumps({"cpython": sys.version.split()[0], "observations": observations}))
