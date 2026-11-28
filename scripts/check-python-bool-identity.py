# SPDX-License-Identifier: MIT
"""Compare the checked stock bool identity assertion with CPython."""

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

DIRECTORY = Path(__file__).resolve().parents[1] / "tests/languages/python"
SUITE = runpy.run_path(str(DIRECTORY / "source-module-entry/check_seeded_run.py"))
INTAKE = runpy.run_path(str(DIRECTORY / "source-scope/check_intake.py"))
PIN = "tests/python/programs/original/k-python/programs/testbools5.py"
SHA = "d88a04924709025fda35c0ffd23e0d1b4aba55ac1795e53b8938f1f4ac422092"

LEAN = SUITE["LEAN"] + """
open Compile.ModuleEntry.Functions.Run.Seeded (legacyListSeed legacyTupleSeed)

private def initialHeap : Core.Closure.Heap := ⟨1, fun address => if address = 0 then some (.int 23) else none⟩

private def boolOutcome (source : Source.Module) (space : Namespace) (status : String)
    (bindings : Bindings) (receipts : List Result) : Bool := Id.run do
  let .ok compiled := Compile.ModuleEntry.Functions.Run.compile source | return false
  let lists : Core.Module.ListHeap := ⟨#[[.int 31]]⟩
  let outcome := Compile.ModuleEntry.Functions.Run.Seeded.run space compiled initialHeap (lists := lists)
  let completion := match outcome.completion with
    | .ok () => "normal"
    | .error (.raised error) => raised error
    | .error .unsupported => "unsupported"
    | .error _ => "unexpected completion"
  return completion == status && outcome.residual.moduleGlobals == bindings &&
    outcome.residual.builtins == space.builtins && outcome.lists == lists &&
    outcome.heap.next == 1 &&
    (outcome.heap.contents 0).map Compile.ModuleEntry.Functions.Run.Seeded.seededValue == some (.int 23) &&
    outcome.calls.map (·.observation.result) == receipts &&
    outcome.calls.all (fun call => call.callee == "bool" && call.observation.caught.isNone)

private def ordinaryBoolOutcome (source : Source.Module) (status : String) (keep : Option Value)
    (mask : Option Value := none) : Bool := Id.run do
  let .ok compiled := Compile.ModuleEntry.Functions.Run.compile source | return false
  let session := Compile.ModuleEntry.Functions.Run.seed .empty initialHeap
  let (events, final) := Compile.ModuleEntry.Functions.Run.runPrefix compiled.table 1000
    (.ready session compiled.instructions)
  let .finished residual (.raised error) := final | return false
  let binding name := (residual.globals name).map Compile.ModuleEntry.Functions.Run.Seeded.seededValue
  return events.isEmpty && raised (.runtime error) == status && binding "keep" == keep &&
    binding "bool" == mask && (binding "tail").isNone && residual.heap.next == 1 &&
    (residual.heap.contents 0).map Compile.ModuleEntry.Functions.Run.Seeded.seededValue == some (.int 23)
"""

STOCK = '(initial "legacy_bool_isinstance_builtin")'
NAME_ERROR = '.error (.raised (.runtime (.nameError "bool")))'
FALSE = ".ok (.bool false)"
TRUE = ".ok (.bool true)"


def cpython(source, builtins, expected, initial=None):
    namespace = dict(initial or {}, __builtins__=builtins)
    result = "normal"
    stdout, stderr = StringIO(), StringIO()
    with redirect_stdout(stdout), redirect_stderr(stderr):
        try:
            exec(compile(source, "<bool fixture>", "exec", dont_inherit=True, optimize=0), namespace)
        except (NameError, TypeError, AssertionError) as error:
            result = SUITE["exception_observation"](error)
    assert not stdout.getvalue() and not stderr.getvalue()
    assert namespace.pop("__builtins__") is builtins
    assert namespace.keys() == expected.keys()
    assert all(type(actual) is type(expected[name]) and actual == expected[name]
               for name, actual in namespace.items()), namespace
    return result


def check(source, source_path, lean_path, *guards):
    INTAKE["emit"](source_path, lean_path, source)
    INTAKE["check_lean"](lean_path, LEAN + "\n".join(guards), extra_imports=SUITE["IMPORTS"])


def outcome(space, result, bindings, receipts):
    return f"#guard boolOutcome pythonSource {space} {json.dumps(result)} {bindings} {receipts}"


def replay_pin(checkout, source_path, lean_path):
    revision = subprocess.check_output(["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()
    assert revision == SUITE["UPSTREAM_REVISION"], revision
    source = SUITE["pinned_source"](checkout, PIN, SHA)
    results = [eval(compile(ast.Expression(statement.test.left), PIN, "eval", optimize=0), {"bool": bool})
               for statement in ast.parse(source).body]
    assert results == [False, True, False] and all(type(value) is bool for value in results)
    guards = ['#guard ordinaryBoolOutcome pythonSource "NameError:bool" none']
    stock_profiles = set(SUITE["BOOL_ISINSTANCE_PROFILES"])
    for profile in ("empty", "legacy_builtin", "legacy_preamble", *SUITE["OPT_IN_PROFILES"]):
        has_bool = profile in stock_profiles
        result = "normal" if has_bool else "NameError:bool"
        assert SUITE["cpython"](source, profile, expected_globals={}) == [result, "absent", "absent"]
        space = f"(initial {json.dumps(profile)})"
        receipts = f"[{FALSE}, {TRUE}, {FALSE}]" if has_bool else f"[{NAME_ERROR}]"
        guards.append(outcome(space, result, f"{space}.moduleGlobals", receipts))
    for seed, builtin in (("legacyListSeed", list), ("legacyTupleSeed", tuple)):
        assert cpython(source, {builtin.__name__: builtin}, {}) == "NameError:bool"
        for placement in ("builtin", "preamble"):
            space = f"({seed} .{placement})"
            guards.append(outcome(space, "NameError:bool", f"{space}.moduleGlobals", f"[{NAME_ERROR}]"))
    check(source, source_path, lean_path, *guards)
    return {"upstream": revision, "path": PIN, "sha256": SHA, "boolean_results": results,
            "stock_seeded": sorted(stock_profiles), "ordinary_and_other_seeds": "NameError:bool"}


def controls(source_path, lean_path):
    stock = {"bool": bool, "int": int}
    failed = 'assert bool(missing_arg) is (missing_right == 0)\n'
    before = 'keep = 7\n'
    after = 'tail = 9\n'
    keep = '[("keep", .int 7)]'
    mask = '[("bool", .none), ("keep", .int 7)]'
    cases = (
        ("missing_before_argument", before + failed + after, "Namespace.empty", {}, {"keep": 7},
         keep, "NameError:bool", "NameError:bool", f"[{NAME_ERROR}]", "none"),
        ("argument_before_mask", before + "bool = None\n" + failed + after, STOCK, stock,
         {"keep": 7, "bool": None}, mask, "NameError:missing_arg", "NameError:missing_arg",
         '[.error (.raised (.runtime (.nameError "missing_arg")))]', "(some .none)"),
        ("mask_before_right", before + "bool = None\nassert bool(0) is (missing_right == 0)\n" + after,
         STOCK, stock, {"keep": 7, "bool": None}, mask, "TypeError", "TypeError",
         "[.error (.raised (.runtime .notCallable))]", "(some .none)"),
        ("right_after_conversion", before + "assert bool(0) is (missing_right == 0)\n" + after,
         STOCK, stock, {"keep": 7}, keep, "NameError:missing_right", "NameError:missing_right", f"[{FALSE}]", None),
        ("false_identity", before + "assert bool(False) is None\n" + after, STOCK, stock,
         {"keep": 7}, keep, "AssertionError:empty", "AssertionError:empty", f"[{FALSE}]", None),
        ("different_descriptor", before + "bool = int\nassert bool(1) is True\n" + after, STOCK, stock,
         {"keep": 7, "bool": int}, '[("bool", .builtin .int), ("keep", .int 7)]',
         "AssertionError:empty", "unsupported", "[.error .unsupported]", None),
    )
    evidence = {}
    for label, source, space, builtins, expected, bindings, python_status, lean_status, receipts, ordinary_mask in cases:
        assert cpython(source, builtins, expected) == python_status, label
        guards = [outcome(space, lean_status, bindings, receipts)]
        if ordinary_mask is not None:
            assert cpython(source, {}, expected) == python_status, label
            guards.append(
                f'#guard ordinaryBoolOutcome pythonSource {json.dumps(lean_status)} (some (.int 7)) {ordinary_mask}')
        check(source, source_path, lean_path, *guards)
        evidence[label] = {"cpython": python_status, "lean": lean_status}

    source = before + "assert bool(0) is (missing_right == 0)\n" + after
    assert cpython(source, stock, {"keep": 7, "bool": (1,)}, {"bool": (1,)}) == "TypeError"
    check(source, source_path, lean_path, outcome(
        f'({STOCK}.bindGlobal "bool" (.returnedTuple [.int 1]))', "TypeError",
        '[("keep", .int 7), ("bool", .returnedTuple [.int 1])]', "[.error (.raised (.runtime .notCallable))]"))
    evidence["returned_tuple_mask"] = {"cpython": "TypeError", "lean": "TypeError"}

    source = ("saved = bool\nbool = None\nbool = saved\nvalue = -7\n"
              "assert bool(value) is (value == -7)\nassert bool(None) is not None\n")
    assert cpython(source, stock, {"saved": bool, "bool": bool, "value": -7}) == "normal"
    check(source, source_path, lean_path, outcome(
        STOCK, "normal", '[("value", .int (-7)), ("bool", .builtin .bool), ("saved", .builtin .bool)]',
        f"[{TRUE}, {FALSE}]"))
    evidence["live_rebinding_and_singletons"] = {"cpython": "normal", "lean": "normal"}

    source = "value = bool()\n"
    assert cpython(source, stock, {"value": False}) == "normal"
    check(source, source_path, lean_path, outcome(STOCK, "normal", '[("value", .bool false)]', f"[{FALSE}]"))
    for source in ("assert bool(1, 2) is True", "assert bool(x=1) is True", "assert bool('x') is True",
                   "assert bool(0) is 0", "assert bool() is False is False"):
        check(source + "\n", source_path, lean_path, """#guard (
  match Compile.ModuleEntry.Functions.Run.compile pythonSource with
  | .error (.source (.scalar .expressionProfile)) => true
  | _ => false)""")
    return evidence


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path, required=True)
    args = parser.parse_args()
    assert sys.version_info[:3] == (3, 13, 5), sys.version
    with tempfile.TemporaryDirectory() as scratch:
        source = Path(scratch) / "Fixture.py"
        lean = source.with_suffix(".lean")
        evidence = {"cpython": sys.version.split()[0], "pin": replay_pin(args.upstream, source, lean),
                    "controls": controls(source, lean)}
    print(json.dumps(evidence))
