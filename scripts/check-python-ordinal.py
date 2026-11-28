# SPDX-License-Identifier: MIT
"""Compare checked Unicode ord with CPython and replay the fixed pin."""

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
PIN = "tests/python/programs/original/k-python/programs/testord.py"
SHA = "e56c02a483c63ad5cde3f2d07ff689add9a336c0f092add1c951ce8b1e3a1df6"

LEAN = SUITE["LEAN"] + """
open Compile.ModuleEntry.Functions.Run.Seeded (legacyListSeed legacyTupleSeed legacyOrdSeed)

private def ordinalHeap : Core.Closure.Heap := ⟨1, fun address => if address = 0 then some (.int 23) else none⟩

private def ordinalOutcome (source : Source.Module) (space : Namespace) (status : String)
    (bindings : Bindings) (receipts : List Result) : Bool := Id.run do
  let .ok compiled := Compile.ModuleEntry.Functions.Run.compile source | return false
  let lists : Core.Module.ListHeap := ⟨#[[.int 31]]⟩
  let outcome := Compile.ModuleEntry.Functions.Run.Seeded.run space compiled ordinalHeap (lists := lists)
  let completion := match outcome.completion with
    | .ok () => "normal"
    | .error (.raised error) => raised error
    | .error .unsupported => "unsupported"
    | .error _ => "unexpected completion"
  return completion == status && outcome.residual.moduleGlobals == bindings &&
    outcome.residual.builtins == space.builtins && outcome.lists == lists && outcome.heap.next == 1 &&
    (outcome.heap.contents 0).map Compile.ModuleEntry.Functions.Run.Seeded.seededValue == some (.int 23) &&
    outcome.calls.map (·.observation.result) == receipts &&
    outcome.calls.all (fun call => call.callee == "ord" && call.observation.caught.isNone)

private def ordinaryOrdinal (source : Source.Module) (status : String) (keep : Option Value)
    (mask : Option Value := none) : Bool := Id.run do
  let .ok compiled := Compile.ModuleEntry.Functions.Run.compile source | return false
  let session := Compile.ModuleEntry.Functions.Run.seed .empty ordinalHeap
  let (events, final) := Compile.ModuleEntry.Functions.Run.runPrefix compiled.table 1000
    (.ready session compiled.instructions)
  let .finished residual (.raised error) := final | return false
  let binding name := (residual.globals name).map Compile.ModuleEntry.Functions.Run.Seeded.seededValue
  return events.isEmpty && raised (.runtime error) == status && binding "keep" == keep &&
    binding "ord" == mask && (binding "tail").isNone && residual.heap.next == 1 &&
    (residual.heap.contents 0).map Compile.ModuleEntry.Functions.Run.Seeded.seededValue == some (.int 23)
"""

STOCK = "(legacyOrdSeed .builtin)"
MISSING = '[.error (.raised (.runtime (.nameError "ord")))]'
TYPE_ERROR = "[.error (.raised (.runtime .notCallable))]"
REJECTED = """#guard (
  match Compile.ModuleEntry.Functions.Run.compile pythonSource with
  | .error (.source (.scalar .expressionProfile)) => true
  | _ => false)"""


def cpython(source, builtins, expected, initial=None):
    namespace = dict(initial or {}, __builtins__=builtins)
    result = "normal"
    stdout, stderr = StringIO(), StringIO()
    with redirect_stdout(stdout), redirect_stderr(stderr):
        try:
            exec(compile(source, "<ord fixture>", "exec", dont_inherit=True, optimize=0), namespace)
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


def receipts(values):
    return "[" + ", ".join(f".ok (.int {value})" for value in values) + "]"


def outcome(space, result, bindings, calls):
    return f"#guard ordinalOutcome pythonSource {space} {json.dumps(result)} {bindings} {calls}"


def replay_pin(checkout, source_path, lean_path):
    revision = subprocess.check_output(["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()
    assert revision == SUITE["UPSTREAM_REVISION"], revision
    source = SUITE["pinned_source"](checkout, PIN, SHA)
    values = [eval(compile(ast.Expression(stmt.test.left), PIN, "eval", optimize=0), {"ord": ord})
              for stmt in ast.parse(source).body]
    assert values == [97, 8224] and all(type(value) is int for value in values)
    guards = ['#guard ordinaryOrdinal pythonSource "NameError:ord" none']
    for profile in ("empty", "legacy_builtin", "legacy_preamble", *SUITE["OPT_IN_PROFILES"]):
        assert SUITE["cpython"](source, profile, expected_globals={}) == ["NameError:ord", "absent", "absent"]
        space = f"(initial {json.dumps(profile)})"
        guards.append(outcome(space, "NameError:ord", f"{space}.moduleGlobals", MISSING))
    for seed, builtin in (("legacyListSeed", list), ("legacyTupleSeed", tuple)):
        assert cpython(source, {builtin.__name__: builtin}, {}) == "NameError:ord"
        for placement in ("builtin", "preamble"):
            space = f"({seed} .{placement})"
            guards.append(outcome(space, "NameError:ord", f"{space}.moduleGlobals", MISSING))
    assert cpython(source, {"ord": ord}, {}) == "normal"
    for placement in ("builtin", "preamble"):
        space = f"(legacyOrdSeed .{placement})"
        guards.append(outcome(space, "normal", f"{space}.moduleGlobals", receipts(values)))
    check(source, source_path, lean_path, *guards)
    return {"upstream": revision, "path": PIN, "sha256": SHA, "integer_results": values,
            "stock_seeded": ["legacy_ord_builtin", "legacy_ord_preamble"],
            "ordinary_and_other_seeds": "NameError:ord"}


def controls(source_path, lean_path):
    stock = {"ord": ord}
    values = [0, 1, 0xd800, 0x10400, 0x10ffff]
    source = "".join(f"assert ord({ascii(chr(value))}) == {value}\n" for value in values)
    source += "assert ord('\\x01') == True\n"
    assert cpython(source, stock, {}) == "normal"
    check(source, source_path, lean_path, outcome(STOCK, "normal", "[]", receipts(values + [1])))
    evidence = {"unicode_results": values}

    cases = (
        ("missing_before_rhs", "", "ord('a') == missing_right", "Namespace.empty", {}, {"keep": 7},
         '[("keep", .int 7)]', "NameError:ord", "NameError:ord", MISSING, "none"),
        ("mask_before_rhs", "ord = None\n", "ord('a') == missing_right", STOCK, stock,
         {"keep": 7, "ord": None}, '[("ord", .none), ("keep", .int 7)]',
         "TypeError", "TypeError", TYPE_ERROR, "(some .none)"),
        ("rhs_after_ordinal", "", "ord('a') == missing_right", STOCK, stock, {"keep": 7},
         '[("keep", .int 7)]', "NameError:missing_right", "NameError:missing_right", receipts([97]), None),
        ("false_inequality", "", "ord('a') != 97", STOCK, stock, {"keep": 7},
         '[("keep", .int 7)]', "AssertionError:empty", "AssertionError:empty", receipts([97]), None),
        ("different_descriptor", "ord = len\n", "ord('a') == 97",
         'Namespace.mk [] [("ord", .builtin .ord), ("len", .builtin .len)]', {"ord": ord, "len": len},
         {"keep": 7, "ord": len}, '[("ord", .builtin .len), ("keep", .int 7)]',
         "AssertionError:empty", "unsupported", "[.error .unsupported]", None),
    )
    for name, prelude, test, space, builtins, wanted, bindings, py_status, lean_status, calls, mask in cases:
        source = f"keep = 7\n{prelude}assert {test}\ntail = 9\n"
        if space.startswith("Namespace.mk"):
            space = f"({space})"
        assert cpython(source, builtins, wanted) == py_status, name
        guards = [outcome(space, lean_status, bindings, calls)]
        if mask is not None:
            assert cpython(source, {}, wanted) == py_status, name
            guards.append(f'#guard ordinaryOrdinal pythonSource {json.dumps(lean_status)} (some (.int 7)) {mask}')
        check(source, source_path, lean_path, *guards)
        evidence[name] = {"cpython": py_status, "lean": lean_status}

    restore = "saved = ord\nord = None\nord = saved\nexpected = 97\nassert ord('a') == expected\n"
    assert cpython(restore, stock, {"saved": ord, "ord": ord, "expected": 97}) == "normal"
    check(restore, source_path, lean_path, outcome(
        STOCK, "normal", '[("expected", .int 97), ("ord", .builtin .ord), ("saved", .builtin .ord)]', receipts([97])))
    evidence["live_rebinding"] = "normal"

    for value in ("", "ab", "e\u0301", "\ud801\udc00"):
        source = f"assert ord({ascii(value)}) == 0\n"
        assert cpython(source, stock, {}) == "TypeError"
        check(source, source_path, lean_path, REJECTED)
    for source in ("assert ord(value) == 97", "assert ord(c='a') == 97", "assert ord('a') < 98",
                   "assert ord('a', 'b') == 97"):
        check(source + "\n", source_path, lean_path, REJECTED)
    evidence["invalid_text_lengths"] = {"cpython": "TypeError", "lean": "expressionProfile"}
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
