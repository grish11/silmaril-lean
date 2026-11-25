# SPDX-License-Identifier: MIT
"""Compare linked ordinary name-table evidence with CPython."""

import argparse
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile


SOURCE = """order_z = 2
order_a = 9
def inspect():
    def probe():
        assert order_z == 2
        x = order_z
        assert order_a == 9
        return x
    def enclosing():
        global order_z
        local = 4
        def child():
            assert local == 4
            return only_child
        assert order_z == 2
        assert "order_z" in probe.__code__.co_names
        return local
    assert "order_z" in probe.__code__.co_names
    assert "co_names" in enclosing.__code__.co_names
    return enclosing

inspected = inspect()
answer = inspected()
"""

CPYTHON = """
import json
import sys
import types

def tables(code):
    yield code.co_names
    for child in code.co_consts:
        if isinstance(child, types.CodeType):
            yield from tables(child)

with open(sys.argv[1], 'rb') as source:
    raw = source.read()
unit = compile(raw, sys.argv[1], 'exec', dont_inherit=True, optimize=0)
scope = {'__builtins__': {}}
exec(unit, scope)
enclosing = scope['inspected']
assert scope['answer'] == 4
assert 'only_child' not in enclosing.__code__.co_names
assert 'local' not in enclosing.__code__.co_names
print(json.dumps([sys.version.split()[0], list(tables(scope['inspect'].__code__))]))
"""

EXPECTED = {
    "3.7.3": [
        ["__code__", "co_names", "AssertionError"],
        ["order_z", "AssertionError", "order_a"],
        ["order_z", "AssertionError", "__code__", "co_names"],
        ["AssertionError", "only_child"],
    ],
    "3.13.5": [
        ["__code__", "co_names"],
        ["order_z", "order_a"],
        ["order_z", "__code__", "co_names"],
        ["only_child"],
    ],
}

LEAN = """
open Silmaril.Languages.Python
open Silmaril.Languages.Python.Compile.Closure

private def linkedTuples (source : Module) (version : CodeNames.Version) :
    Option (List (List String)) := do
  let checked ← (Compile.ModuleEntry.Functions.check source).toOption
  let (_, blocks) ← (Compile.ModuleEntry.Functions.Run.lowerInstructions checked.tree 0 checked.actions).toOption
  (blocks.zipIdx).mapM fun (block, key) => do
    let evidence ← CodeNames.checked? checked.tree blocks ⟨key, block.entry.layout⟩
    return evidence.tuple version

private def executed (source : Module) : Option (List (List String)) := do
  let compiled ← (Compile.ModuleEntry.Functions.Run.compile source).toOption
  let .finished session .normal :=
    (Compile.ModuleEntry.Functions.Run.runPrefix compiled.table 256 compiled.start).2 | none
  let some (.int 4) := session.globals "answer" | none
  compiled.entries.mapM fun entry => do
    let data ← entry.definition.codeNames
    if data.profile == .cpython3135ExecOptimize0 then some data.names else none
"""

GUARD_SOURCE = r'''def inspect(receiver):
    assert "\ud800" in receiver.__code__.co_names
'''

GUARD_LEAN = """
open Silmaril.Languages.Python
open Silmaril.Languages.Python.Compile.Closure

#guard (match Body.compile pythonSource with
  | .ok compiled => match (Link.link compiled).blocks[0]? with
    | some block => match block.entry.definition.body with
      | .assertCodeNames (.read _) [55296] _ => true
      | _ => false
    | none => false
  | .error _ => false)

#guard (Body.codeNamesTest?
  (.comparison (.text [97]) [(.notIn, .attribute (.attribute (.name "f") "__code__") "co_names")])).isNone

#guard (CodeNames.readOperations? (.globalName (layout := ⟨0, 0, 0⟩) "__debug__")).isNone
"""


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cpython", action="append", default=[], help="additional CPython executable")
    options = parser.parse_args()
    shared = runpy.run_path(str(Path(__file__).resolve().parent.parent / "source-scope/check_intake.py"))
    modules = (
        "Compile.Closure.CodeNames.Defs",
        "Compile.Closure.Link.Defs",
        "Compile.Closure.Body.Defs",
        "Compile.ModuleEntry.Functions.Defs",
        "Compile.ModuleEntry.Functions.Run.Defs",
        "Core.Closure.Dispatch.Defs",
    )
    imports = tuple(f"{prefix} Silmaril.Languages.Python.{module}"
                    for module in modules for prefix in ("import", "meta import"))
    with tempfile.TemporaryDirectory() as temporary:
        source_file = Path(temporary) / "Example.py"
        lean_file = Path(temporary) / "Example.lean"
        shared["emit"](source_file, lean_file, SOURCE)
        for executable in [sys.executable, *options.cpython]:
            result = subprocess.run([executable, "-I", "-c", CPYTHON, str(source_file)], check=True,
                                    text=True, capture_output=True, timeout=10)
            version, tuples = json.loads(result.stdout)
            assert result.stderr == ""
            if version in EXPECTED:
                assert tuples == EXPECTED[version], (version, tuples)
                print(f"CPython {version} reproduced the exact linked-name fixture tuples.")
        checks = LEAN + "\n".join(
            f"#guard linkedTuples pythonSource .{tag} == some {json.dumps(EXPECTED[version])}"
            for tag, version in (("cpython373", "3.7.3"), ("cpython3135", "3.13.5"))
        )
        checks += f"\n#guard executed pythonSource == some {json.dumps(EXPECTED['3.13.5'])}"
        shared["check_lean"](lean_file, checks, extra_imports=imports)
        shared["emit"](source_file, lean_file, GUARD_SOURCE)
        shared["check_lean"](lean_file, GUARD_LEAN, extra_imports=imports)
