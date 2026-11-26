# SPDX-License-Identifier: MIT
"""Replay the checked normally-completing try profile on CPython and Lean."""

import argparse
from contextlib import redirect_stderr, redirect_stdout
from io import StringIO
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile
import warnings


DIRECTORY = Path(__file__).resolve().parents[1] / "tests/languages/python"
SUITE = runpy.run_path(str(DIRECTORY / "source-module-entry/check_seeded_run.py"))
INTAKE = runpy.run_path(str(DIRECTORY / "source-scope/check_intake.py"))
PREFIX = "tests/python/programs/original/lambda-py/python-reference/exceptions"
PINS = (
    ("try-finally-no-exception.py", "8067173cbe5004ea78f325bb286a09d0b3d66aa72653873d8ea86c3f4ad97e39",
     {"hit_finally": True}, "___assertTrue"),
    ("test-try-except-no-exception.py", "6dc0744b2ba31dc1db337bf8d4b1c5280827d607ac3fe942f5b19d05a1d07798",
     {"hit_except": False}, "___assertFalse"),
    ("try-except-else-no-exception.py", "fba1895ec66a8bfe62e9f9acf8976fcbaa034e30e5634ace84e4eb468937ddf2",
     {"hit_except": False, "hit_else": True}, "___assertFalse"),
    ("try-except-finally-no-exception.py", "128e5af8b5f72e6e477bb27dd9e824754087f41ef209ef3283052302d5325d44",
     {"hit_except": False, "hit_finally": True}, "___assertFalse"),
    ("try-except-else-finally-no-exception.py", "56c4c7ff6cf0039816e146a73c02ca5d8087506258c156a9533837e925d47f58",
     {"hit_except": False, "hit_else": True, "hit_finally": True}, "___assertFalse"),
)

LEAN = SUITE["LEAN"] + """
open Compile.ModuleEntry.Functions.Run.Seeded (legacyTupleIdentitySeed)

private def tryHeap : Core.Closure.Heap := ⟨1, fun slot => if slot == 0 then some (.int 23) else none⟩
private def tryLists : Core.Module.ListHeap := ⟨#[[.int 31]]⟩

private def trySeeded (source : Source.Module) (space : Namespace) (status : String)
    (bindings : Bindings) (receipts : List (String × Result)) : Bool := Id.run do
  let .ok compiled := Compile.ModuleEntry.Functions.Run.compile source | return false
  let result := Compile.ModuleEntry.Functions.Run.Seeded.run space compiled tryHeap (lists := tryLists)
  let actual := match result.completion with
    | .ok () => "normal"
    | .error (.raised error) => raised error
    | .error _ => "outside profile"
  let expected := bindings ++ space.moduleGlobals
  return actual == status && result.residual.moduleGlobals.length == expected.length &&
    expected.all (fun (name, value) =>
      Core.Module.SeededCall.lookupBinding result.residual.moduleGlobals name == some value) &&
    result.residual.builtins == space.builtins &&
    result.heap.next == tryHeap.next && (result.heap.contents 0).map
      Compile.ModuleEntry.Functions.Run.Seeded.seededValue == some (.int 23) &&
    result.lists == tryLists && result.calls.all (·.observation.caught.isNone) &&
    result.calls.map (fun call => (call.callee, call.observation.result)) == receipts

private def tryOrdinary (source : Source.Module) (status : Compile.ModuleEntry.Functions.Run.Completion)
    (bindings : Bindings) (missingHelper : Bool := false) : Bool := Id.run do
  let .ok compiled := Compile.ModuleEntry.Functions.Run.compile source | return false
  let input := { Compile.ModuleEntry.Functions.Run.seed .empty tryHeap with lists := tryLists }
  let (events, state) := Compile.ModuleEntry.Functions.Run.runPrefix compiled.table 1000
    (.ready input compiled.instructions)
  let .finished residual actual := state | return false
  let globals := compiled.checked.tree.scope.context.assigned.eraseDups.filterMap fun name =>
    (residual.globals name).map fun value => (name, Compile.ModuleEntry.Functions.Run.Seeded.seededValue value)
  let exactEvents := if missingHelper then
    match events, status with
    | [.complete (.error reached)], .raised expected => decide (reached = expected)
    | _, _ => false
  else events.isEmpty
  return actual == status && exactEvents && globals.length == bindings.length &&
    bindings.all (fun pair => globals.contains pair) &&
    residual.heap.next == tryHeap.next && (residual.heap.contents 0).map
      Compile.ModuleEntry.Functions.Run.Seeded.seededValue == some (.int 23) && residual.lists == tryLists
"""


def execute(source, expected, *, builtins=None, initial=None):
    builtins = {} if builtins is None else builtins
    namespace = dict(initial or {}, __builtins__=builtins)
    completion = "normal"
    with redirect_stdout(StringIO()) as stdout, redirect_stderr(StringIO()) as stderr:
        with warnings.catch_warnings(record=True) as emitted:
            warnings.simplefilter("always")
            unit = compile(source, "<normal try>", "exec", dont_inherit=True, optimize=0)
        try:
            exec(unit, namespace)
        except (NameError, AssertionError) as error:
            completion = SUITE["exception_observation"](error)
    assert not emitted and not stdout.getvalue() and not stderr.getvalue()
    assert namespace.pop("__builtins__") is builtins
    wanted = dict(initial or {}) | expected
    assert namespace.keys() == wanted.keys()
    assert all(type(value) is type(wanted[name]) and value == wanted[name]
               for name, value in namespace.items()), namespace
    return completion


def bindings(values):
    pairs = []
    for name, value in values.items():
        if type(value) is bool:
            code = ".bool " + str(value).lower()
        elif type(value) is int:
            code = f".int ({value})"
        else:
            assert value is None
            code = ".none"
        pairs.append(f"({json.dumps(name)}, {code})")
    return "[" + ", ".join(pairs) + "]"


def guard_pair(expected, ordinary, seeded):
    bound = bindings(expected)
    return (f"#guard tryOrdinary pythonSource ({ordinary}) {bound}\n"
            f'#guard trySeeded pythonSource .empty {json.dumps(seeded)} {bound} []')


def replay_pins(checkout):
    revision = subprocess.check_output(
        ["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True
    ).strip()
    assert revision == SUITE["UPSTREAM_REVISION"], revision
    truth = SUITE["pinned_truth_helper"](checkout)
    fixtures = []
    report = {}
    for filename, digest, expected, helper in PINS:
        path = f"{PREFIX}/{filename}"
        source = SUITE["pinned_source"](checkout, path, digest)
        raw = (checkout / path).read_bytes()
        assert source.encode("utf-8") == raw
        missing = f"NameError:{helper}"
        bound = bindings(expected)
        assert execute(raw, expected) == missing
        guards = [f'#guard tryOrdinary pythonSource (.raised (.nameError "{helper}")) {bound} true']
        for profile in ("empty", "legacy_builtin", "legacy_preamble"):
            assert SUITE["cpython"](raw, profile, expected_globals=expected)[0] == missing
            guards.append(f'#guard trySeeded pythonSource (initial "{profile}") "{missing}" {bound} '
                          f'[("{helper}", .error (.raised (.runtime (.nameError "{helper}"))))]')
        evidence = {"sha256": digest, "bindings": expected, "fixed": missing}
        if helper == "___assertTrue":
            for placement in ("builtin", "preamble"):
                trace = []

                def observe(value):
                    assert type(value) is bool
                    trace.append(value)
                    return truth(value)

                supplied = {helper: observe}
                fallback, initial = (supplied, {}) if placement == "builtin" else ({}, supplied)
                assert execute(raw, expected, builtins=fallback, initial=initial) == "normal"
                assert trace == [True]
                guards.append(f'#guard trySeeded pythonSource (legacyTupleIdentitySeed .{placement}) "normal" '
                              f'{bound} [("{helper}", .ok .none)]')
            evidence["true_helper_placements"] = "normal"
        report[filename] = evidence
        fixtures.append((source, "\n".join(guards)))
    return fixtures, report


def controls():
    fixtures = []
    source = """flag = False
try:
    flag = True
    order = 1
    value = None
except:
    handler = 8
else:
    order = 2
finally:
    snapshot = order
    order = 3
after = 9
"""
    expected = {"flag": True, "order": 3, "value": None, "snapshot": 2, "after": 9}
    assert execute(source, expected) == "normal"
    fixtures.append((source, guard_pair(expected, ".normal", "normal")))

    source = """replaced = 10
try:
    body = 1
except:
    handler = 8
else:
    phase = 2
finally:
    retained = phase
    replaced = missing
    late = 6
after = 9
"""
    expected = {"replaced": 10, "body": 1, "phase": 2, "retained": 2}
    assert execute(source, expected) == "NameError:missing"
    fixtures.append((source, guard_pair(expected, '.raised (.nameError "missing")', "NameError:missing")))

    source = """try:
    pass
finally:
    retained = True
    assert False
after = 9
"""
    expected = {"retained": True}
    assert execute(source, expected) == "AssertionError:empty"
    fixtures.append((source, guard_pair(expected, ".assertionError", "AssertionError:empty")))

    rejected = (
        ("try:\n    reached = missing\nexcept:\n    caught = True\n", {"caught": True}, "normal"),
        ("try:\n    pass\nexcept:\n    handler = True\nelse:\n    reached = missing\nfinally:\n    cleaned = True\n",
         {"cleaned": True}, "NameError:missing"),
        ("try:\n    pass\nexcept Missing:\n    handler = True\n", {}, "normal"),
    )
    for source, expected, status in rejected:
        assert execute(source, expected) == status
        fixtures.append((source, """#guard (match Compile.ModuleEntry.Functions.Run.compile pythonSource with
  | .error (.source (.scalar .statementProfile)) => true
  | _ => false)"""))
    return fixtures


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path, required=True)
    args = parser.parse_args()
    assert sys.version_info[:3] == (3, 13, 5), sys.version
    fixtures, pins = replay_pins(args.upstream)
    control_fixtures = controls()
    with tempfile.TemporaryDirectory() as scratch:
        source = Path(scratch) / "Fixture.py"
        INTAKE["check_lean_batch"](source, source.with_suffix(".lean"), fixtures + control_fixtures,
                                   LEAN, extra_imports=SUITE["IMPORTS"])
    print(json.dumps({"cpython": "3.13.5", "pins": pins, "controls": len(control_fixtures)}))
