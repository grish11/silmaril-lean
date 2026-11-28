# SPDX-License-Identifier: MIT
"""Compare checked literal dictionary get with CPython through both runners."""

import argparse
import ast
from contextlib import redirect_stderr, redirect_stdout
from io import StringIO
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile

TESTS = Path(__file__).resolve().parents[1] / "tests/languages/python"
INTAKE = runpy.run_path(str(TESTS / "source-scope/check_intake.py"))
SUITE = runpy.run_path(str(TESTS / "source-module-entry/check_seeded_run.py"))
PIN = "tests/python/programs/original/k-python/programs/testdicts2.py"
SHA256 = "8b67ae2dca7b6deb480e706b297d4c70f088b9abf3638e39aec4b7df6dac7cb7"
HELPER = "___assertEqual"

LEAN = """
open Silmaril.Languages.Python
open Core.Module.SeededCall
open Compile.ModuleEntry.Functions.Run (Completion compile runPrefix seed)

private def heap : Core.Closure.Heap := ⟨1, fun address => if address = 0 then some (.int 23) else none⟩
private def lists : Core.Module.ListHeap := ⟨#[[.int 31]]⟩

private def retains (reached : Core.Closure.Heap) : Bool :=
  reached.next == 1 && (reached.contents 0).map Compile.ModuleEntry.Functions.Run.Seeded.seededValue == some (.int 23)

private def ordinaryGet (source : Source.Module) (completion : Completion)
    (bindings : List (String × Option Value)) (callFailed : Bool) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let (events, result) := runPrefix compiled.table 100 (.ready { seed .empty heap with lists } compiled.instructions)
  let .finished residual reached := result | return false
  let exactEvents := match events, completion with
    | [.complete (.error error)], .raised expected => callFailed && error == expected
    | [], _ => !callFailed
    | _, _ => false
  return reached == completion && exactEvents && retains residual.heap && residual.lists == lists &&
    bindings.all fun (name, value) =>
      (residual.globals name).map Compile.ModuleEntry.Functions.Run.Seeded.seededValue == value

private def seededGet (source : Source.Module) (space : Namespace)
    (completion : Except Compile.ModuleEntry.Functions.Run.Seeded.ModuleFailure Unit)
    (bindings : Bindings) (calls : List (String × Result)) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let result := Compile.ModuleEntry.Functions.Run.Seeded.run space compiled heap (lists := lists)
  return result.completion == completion && result.residual.moduleGlobals == bindings ++ space.moduleGlobals &&
    result.residual.builtins == space.builtins && retains result.heap && result.lists == lists &&
    result.calls.map (fun call => (call.callee, call.observation.result)) == calls &&
    result.calls.all (fun call => call.observation.caught.isNone)
"""

PROFILES = {
    "empty": "Namespace.empty",
    **{name: f"(Compile.ModuleEntry.Functions.Run.Seeded.legacyTextSeed .{name})"
       for name in ("builtin", "preamble")},
}


def cpython(source, profile):
    calls = []

    def equal(left, right):
        assert type(left) is type(right) is int and left == right
        calls.append(left)

    builtins = {}
    namespace = {"__builtins__": builtins}
    placement = builtins if profile == "builtin" else namespace
    if profile in ("builtin", "preamble"):
        placement[HELPER] = equal
    with redirect_stdout(StringIO()) as stdout, redirect_stderr(StringIO()) as stderr:
        try:
            exec(compile(source, "<literal dictionary get>", "exec", dont_inherit=True, optimize=0), namespace)
            status = "normal"
        except NameError as error:
            status = f"NameError:{error.name}"
        except (AssertionError, TypeError) as error:
            status = type(error).__name__
    assert stdout.getvalue() == stderr.getvalue() == ""
    assert namespace.pop("__builtins__") is builtins
    if profile in ("builtin", "preamble"):
        assert placement.pop(HELPER) is equal
    return status, namespace, calls


def lean_value(value):
    if type(value) is bool:
        return f".bool {str(value).lower()}"
    if type(value) is int:
        return f".int ({value})"
    assert value is None
    return ".none"


def guard_case(source, expected, *, helper=False):
    names = dict.fromkeys(node.id for node in ast.walk(ast.parse(source))
                          if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store))
    guards, observations = [], {}
    for profile in ("ordinary", *PROFILES):
        status, bindings, calls = cpython(source, profile)
        if helper:
            assert (status, calls) == (("normal", [17]) if profile in ("builtin", "preamble")
                                       else (f"NameError:{HELPER}", []))
        else:
            assert status == expected and not calls
        name_error = status.removeprefix("NameError:") if status.startswith("NameError:") else None
        if profile == "ordinary":
            completion = f".raised (.nameError {json.dumps(name_error)})" if name_error else (
                ".assertionError" if status == "AssertionError" else ".normal")
            residual = ", ".join(f"({json.dumps(name)}, "
                                 + (f"some ({lean_value(bindings[name])})" if name in bindings else "none") + ")"
                                 for name in names)
            guards.append(f"#guard ordinaryGet pythonSource ({completion}) [{residual}] {str(helper).lower()}")
        else:
            completion = ".ok ()"
            receipts = ", ".join(f'("{HELPER}", .ok .none)' for _ in calls)
            if name_error:
                raised = f".raised (.runtime (.nameError {json.dumps(name_error)}))"
                completion = f".error ({raised})"
                if helper:
                    receipts = f'("{HELPER}", .error ({raised}))'
            elif status == "AssertionError":
                completion = ".error (.raised (.assertionError .empty))"
            residual = ", ".join(f"({json.dumps(name)}, {lean_value(value)})"
                                 for name, value in reversed(list(bindings.items())))
            guards.append(f"#guard seededGet pythonSource {PROFILES[profile]} ({completion}) [{residual}] [{receipts}]")
        observations[profile] = {"status": status, "bindings": {name: lean_value(value)
                                 for name, value in bindings.items()}, "helper_operands": calls}
    return (source, "\n".join(guards)), observations


def controls(upstream):
    fixtures, observations = [], {}
    for label, source, expected, helper in (
        ("exact tags and duplicate keys", """
dict = 91
get = 92
last = {1: 7, True: False, 1: None}.get(True, -2)
zero = {False: -7, 0: True}.get(False)
none_key = {None: -4, 0: -2}.get(None)
negative_key = {-5: 19}.get(-5, 3)
implicit = {}.get(5)
explicit = {8: 9}.get(5, False)
assert last == None
assert zero == True
""", "normal", False),
        ("retained binding through assertion error", """
kept = {1: 2}.get(1, 99)
assert {}.get(1, False) is True
tail = 9
""", "AssertionError", False),
        ("retained binding through enclosing lookup error", """
kept = {}.get(1, False)
result = {1: 2}.get(1) == missing
tail = 9
""", "NameError:missing", False),
        ("existing call operand", "___assertEqual({1: 17}.get(True, 9), 17)\n", None, True),
    ):
        fixture, observed = guard_case(source, expected, helper=helper)
        fixtures.append(fixture)
        observations[label] = observed
    if upstream is not None:
        source = SUITE["pinned_source"](upstream, PIN, SHA256)
        fixture, observed = guard_case(source, "normal")
        fixtures.append(fixture)
        observations["unchanged pin"] = {"sha256": SHA256, "profiles": observed}

    rejection = """#guard (match compile pythonSource with
  | .error (.source (.scalar .expressionProfile)) => true
  | _ => false)"""
    for expression, expected in (
        ("{1: 4}.get(1, fallback)", "NameError:fallback"),
        ("{1: 4, 2: other}.get(1, fallback)", "NameError:other"),
        ("{**source}.get(1)", "NameError:source"),
        ("{}.get(key=1)", "TypeError"),
        ("{}.get()", "TypeError"),
        ("{}.get(*items)", "NameError:items"),
        ("{[1]: 4}.get(1)", "TypeError"),
    ):
        source = f"result = {expression}\n"
        assert cpython(source, "ordinary") == (expected, {}, [])
        fixtures.append((source, rejection))
        observations[expression] = {"cpython": expected, "lean": "scalar.expressionProfile"}
    return fixtures, observations


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path)
    args = parser.parse_args()
    assert sys.implementation.name == "cpython", sys.version
    revision = None
    if args.upstream is not None:
        assert sys.version_info[:3] == (3, 13, 5), sys.version
        revision = subprocess.check_output(["git", "-C", str(args.upstream), "rev-parse", "HEAD"], text=True).strip()
        assert revision == SUITE["UPSTREAM_REVISION"]
    fixtures, observations = controls(args.upstream)
    with tempfile.TemporaryDirectory() as directory:
        source, lean = Path(directory) / "Fixture.py", Path(directory) / "Fixtures.lean"
        INTAKE["check_lean_batch"](source, lean, fixtures, LEAN, extra_imports=SUITE["IMPORTS"])
    print(json.dumps({"cpython": sys.version.split()[0], "upstream": revision,
                      "fixtures": len(fixtures), "observations": observations}))
