# SPDX-License-Identifier: MIT
"""Replay reached checked integer division through both module runners."""

import argparse
import ast
from contextlib import redirect_stderr, redirect_stdout
import hashlib
from io import StringIO
import json
from pathlib import Path
import runpy
import struct
import subprocess
import sys
import tempfile
from types import FunctionType

ROOT = Path(__file__).resolve().parents[1]
TESTS = ROOT / "tests/languages/python"
INTAKE = runpy.run_path(str(TESTS / "source-scope/check_intake.py"))
SUITE = runpy.run_path(str(TESTS / "source-module-entry/check_seeded_run.py"))
QUOTIENT = runpy.run_path(str(ROOT / "scripts/check-python-integer-true-division.py"))

LEAN = """
open Silmaril.Languages.Python
open Compile.ModuleEntry.Functions.Run (Completion compile runPrefix seed)
open Core.Module.SeededCall (Namespace Result Value lookupBinding)

private def initialHeap : Core.Closure.Heap :=
  ⟨1, fun address => if address = 0 then some (.int 23) else none⟩

private def retained (heap : Core.Closure.Heap) : Bool :=
  heap.next == 1 &&
  (heap.contents 0).map Compile.ModuleEntry.Functions.Run.Seeded.seededValue == some (.int 23)

private def divisionSeed (placement : Compile.ModuleEntry.Functions.Run.Seeded.SeedPlacement) : Namespace :=
  let space := Compile.ModuleEntry.Functions.Run.Seeded.legacySeed placement
  { space with builtins := ("relay", .builtin .int) :: space.builtins }

private def functionsAre (lookup : String → Option Value) (names : List String) : Bool :=
  names.all fun name => match lookup name with | some (.function _) => true | _ => false

private def ordinaryDivision (source : Source.Module) (completion : Completion)
    (values : List (String × Value)) (functions absent : List String) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let (_, final) := runPrefix compiled.table 1000 (.ready (seed .empty initialHeap) compiled.instructions)
  let .finished residual result := final | return false
  let lookup := fun name => (residual.globals name).map Compile.ModuleEntry.Functions.Run.Seeded.seededValue
  return result == completion && retained residual.heap &&
    values.all (fun (name, value) => lookup name == some value) &&
    functionsAre lookup functions && absent.all (fun name => (lookup name).isNone)

private def seededDivision (source : Source.Module) (space : Namespace)
    (completion : Except Compile.ModuleEntry.Functions.Run.Seeded.ModuleFailure Unit)
    (values : List (String × Value)) (functions : List String) (receipts : List (String × Result)) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let lists : Core.Module.ListHeap := ⟨#[[.int 31]]⟩
  let result := Compile.ModuleEntry.Functions.Run.Seeded.run space compiled initialHeap (lists := lists)
  let lookup := lookupBinding result.residual.moduleGlobals
  let overwritten := values.map Prod.fst ++ functions
  let expected := values ++ space.moduleGlobals.filter (fun binding => !overwritten.contains binding.1)
  return result.completion == completion && retained result.heap && result.lists == lists &&
    result.residual.builtins == space.builtins &&
    result.residual.moduleGlobals.length == expected.length + functions.length &&
    expected.all (fun (name, value) => lookup name == some value) && functionsAre lookup functions &&
    result.calls.map (fun receipt => (receipt.callee, receipt.observation.result)) == receipts &&
    result.calls.all (fun receipt => receipt.observation.caught.isNone)
"""

RELAY = "def relay(value):\n    return value\n"
PREFIX = "kept = 7\n" + RELAY + "result = relay(0 / -3)\n"
PROFILES = (
    ("empty", "Namespace.empty"),
    ("builtin", "(divisionSeed .builtin)"),
    ("preamble", "(divisionSeed .preamble)"),
)


INT_DIVMOD_CASES = (
    (5, 2, 2, 1), (-5, 2, -3, 1), (5, -2, -3, -1), (-5, -2, 2, -1),
    (-6, 2, -3, 0), (6, -2, -3, 0), (0, -2, 0, 0),
    (-(2**160 + 5), 2**80, -(2**80 + 1), 2**80 - 5),
)


def assertion_equal(left, right):
    assert left == right


def cpython(source, profile):
    builtins = {"relay": int} if profile in ("builtin", "preamble") else {}
    namespace = {"__builtins__": builtins}
    if profile == "builtin":
        builtins["___assertEqual"] = assertion_equal
    elif profile == "preamble":
        namespace["___assertEqual"] = assertion_equal
    with redirect_stdout(StringIO()) as stdout, redirect_stderr(StringIO()) as stderr:
        try:
            exec(compile(source, "<division call>", "exec", dont_inherit=True, optimize=0), namespace)
            result = "normal"
        except NameError as error:
            result = f"NameError:{error.name}"
        except (ZeroDivisionError, OverflowError, TypeError) as error:
            result = type(error).__name__
    assert stdout.getvalue() == stderr.getvalue() == ""
    assert namespace.pop("__builtins__") is builtins
    if profile == "preamble":
        assert namespace.pop("___assertEqual") is assertion_equal
    return result, namespace


def bits(value):
    assert type(value) is float
    return struct.pack(">d", value).hex()


def lean_value(value):
    if type(value) is float:
        return f".float64 ⟨Silmaril.Numeric.Ieee754.F64.ofBits 0x{bits(value)}, by decide⟩"
    if type(value) is int:
        return f".int ({value})"
    assert value is None
    return ".none"


def literal_list(values):
    return "[" + ", ".join(values) + "]"


def ordinary(completion, values, functions, absent):
    return f"#guard ordinaryDivision pythonSource ({completion}) {values} {functions} {absent}"


def seeded(space, completion, values, functions, calls):
    return f"#guard seededDivision pythonSource {space} ({completion}) {values} {functions} {calls}"


def state(namespace):
    values = literal_list(f"({json.dumps(name)}, {lean_value(value)})" for name, value in namespace.items()
                          if type(value) is not FunctionType)
    functions = json.dumps([name for name, value in namespace.items() if type(value) is FunctionType])
    return values, functions


def receipt(name, result):
    return f"({json.dumps(name)}, {result})"


def success_receipt(name, value):
    return receipt(name, f".ok ({lean_value(value)})")


def error_receipt(name, error):
    return receipt(name, f".error (.raised (.runtime ({error})))")


def guards_for(source, status, error, make_receipts):
    observed, namespace = cpython(source, "ordinary")
    assert observed == status
    summary = {name: bits(value) if type(value) is float else value for name, value in namespace.items()
               if type(value) is not FunctionType}
    values, functions = state(namespace)
    writes = {node.id for node in ast.walk(ast.parse(source)) if isinstance(node, ast.Name)
              and isinstance(node.ctx, ast.Store)}
    completion = ".normal" if error is None else f".raised ({error})"
    guards = [ordinary(completion, values, functions, json.dumps(sorted(writes - namespace.keys())))]
    seeded_result = ".ok ()" if error is None else f".error (.raised (.runtime ({error})))"
    calls = literal_list(make_receipts(namespace))
    for profile, space in PROFILES:
        reached, residual = cpython(source, profile)
        assert reached == status and state(residual) == (values, functions)
        guards.append(seeded(space, seeded_result, values, functions, calls))
    return (source, "\n".join(guards)), summary


def controls(upstream):
    fixtures = []
    observed = {}
    source = ("kept = 7\n" + RELAY + "saved = relay\nrelay = 4\n"
              "normal = saved(5 / 2)\nnegative_zero = saved(0 / -3)\nsubnormal = saved(3 / 2**1075)\n"
              "rounded = saved(9007199254740987 / 9007199254740993)\ncopied = saved(normal)\ntail = 9\n")
    fields = ("normal", "negative_zero", "subnormal", "rounded", "copied")
    fixture, outcome = guards_for(source, "normal", None,
                                  lambda ns: [success_receipt("saved", ns[name]) for name in fields])
    assert [outcome[name] for name in fields] == [
        "4004000000000000", "8000000000000000", "0000000000000002", "3feffffffffffffa",
        "4004000000000000"]
    fixtures.append(fixture)
    observed["transport"] = outcome

    for label, statement, settled, status, error in (
        ("zero", "bad = relay(1 / 0)", None, "ZeroDivisionError", ".arithmetic .zeroDivisionError"),
        ("overflow", "bad = relay(2**1024 / 1)", None, "OverflowError", ".overflowError"),
        ("missing callee", "bad = missing(1 / 0)", None, "NameError:missing", '.nameError "missing"'),
        ("masked callee", "relay = 0\nbad = relay(1 / 0)", None, "ZeroDivisionError",
         ".arithmetic .zeroDivisionError"),
        ("float callee", "bad = result(1 / 2)", "result", "TypeError", ".notCallable"),
        ("arity", "def wrong(x, y):\n    return x\nbad = wrong(1 / 2)", "wrong", "TypeError", ".positionalArity 2 1"),
        ("left lookup", "bad = relay(missing, 1 / 0)", None, "NameError:missing", '.nameError "missing"'),
        ("left division", "bad = relay(1 / 0, missing)", None, "ZeroDivisionError", ".arithmetic .zeroDivisionError"),
    ):
        failed = [] if settled is None else [error_receipt(settled, error)]
        fixture, outcome = guards_for(PREFIX + statement + "\ntail = 9\n", status, error,
                                      lambda ns: [success_receipt("relay", ns["result"])] + failed)
        assert outcome["kept"] == 7 and outcome["result"] == "8000000000000000" and "tail" not in outcome
        fixtures.append(fixture)
        observed[label] = outcome

    source = "kept = 7\n" + RELAY + "saved = relay\nrelay = 4\n"
    expected = {}
    for index, (numerator, divisor, quotient, remainder) in enumerate(INT_DIVMOD_CASES):
        for field, op, result in (("quotient", "//", quotient), ("remainder", "%", remainder)):
            name = f"{field}_{index}"
            source += f"{name} = saved({numerator} {op} {divisor})\n"
            expected[name] = result
    # The ordinary runner supports this linked integer-returning call.
    # The seeded differential checks the same operands through stock helpers.
    status, namespace = cpython(source, "ordinary")
    assert status == "normal"
    assert {name: namespace[name] for name in expected} == expected
    values, functions = state(namespace)
    fixtures.append((source, ordinary(".normal", values, functions, "[]")))
    observed["ordinary integer floor quotient and remainder"] = expected

    for label, statement, status, error in (
        ("floor division by zero", "bad = relay(1 // (2 - 2))",
         "ZeroDivisionError", ".arithmetic .zeroDivisionError"),
        ("modulo by zero", "bad = relay(1 % 0)", "ZeroDivisionError", ".arithmetic .zeroDivisionError"),
        ("missing callee before floor division", "bad = missing(1 // 0)",
         "NameError:missing", '.nameError "missing"'),
        ("floor division before callability and right lookup", "relay = 0\nbad = relay(1 // 0, missing)",
         "ZeroDivisionError", ".arithmetic .zeroDivisionError"),
        ("left lookup before modulo", "bad = relay(missing, 1 % 0)",
         "NameError:missing", '.nameError "missing"'),
    ):
        fixture, outcome = guards_for(PREFIX + statement + "\ntail = 9\n", status, error,
                                      lambda ns: [success_receipt("relay", ns["result"])])
        assert outcome["kept"] == 7 and outcome["result"] == "8000000000000000" and "tail" not in outcome
        fixtures.append(fixture)
        observed[label] = outcome

    for body in ("assert value == 1", "return value + 1"):
        source = PREFIX + f"def consume(value):\n    {body}\nconsume(3 / 3)\ntail = 9\n"
        status, namespace = cpython(source, "ordinary")
        assert status == "normal" and namespace.pop("tail") == 9
        values, functions = state(namespace)
        guards = [ordinary(".executorFault .unsupportedFloatOperand", values, functions, '["tail"]')]
        for _, space in PROFILES:
            guards.append(seeded(space, ".error (.directCallFault .unsupportedFloatOperand)", values, functions,
                                 literal_list([success_receipt("relay", namespace["result"])])))
        fixtures.append((source, "\n".join(guards)))

    source = PREFIX + "___assertEqual(relay(5 / 2), missing)\ntail = 9\n"
    status, ns = cpython(source, "ordinary")
    assert status == "NameError:___assertEqual" and "tail" not in ns
    values, functions = state(ns)
    outer = [success_receipt("relay", ns["result"])]
    guards = [ordinary('.raised (.nameError "___assertEqual")', values, functions, '["tail"]')]
    guards.append(seeded("Namespace.empty", '.error (.raised (.runtime (.nameError "___assertEqual")))',
                         values, functions, literal_list(outer)))
    for profile, space in PROFILES[1:]:
        status, namespace = cpython(source, profile)
        assert status == "NameError:missing" and state(namespace) == (values, functions)
        guards.append(seeded(space, '.error (.raised (.runtime (.nameError "missing")))', values, functions,
                             literal_list(outer + [success_receipt("relay", 2.5)])))
    fixtures.append((source, "\n".join(guards)))

    source = RELAY + "ratio = relay(1.0 / 2)\nrelay(1.0 / 2)\n"
    fixture, outcome = guards_for(source, "normal", None,
                                  lambda ns: [success_receipt("relay", ns["ratio"])] * 2)
    assert outcome["ratio"] == "3fe0000000000000"
    fixtures.append(fixture)
    observed["mixed transport"] = outcome

    rejected = """#guard (match compile pythonSource with
  | .error (.source (.scalar .expressionProfile)) => true
  | _ => false)"""
    fixtures.append((RELAY + "relay(value / 2)\n", rejected))
    if upstream is not None:
        raw = (upstream / QUOTIENT["PIN"]).read_bytes()
        assert hashlib.sha256(raw).hexdigest() == QUOTIENT["SHA256"]
        line = raw.decode().splitlines(keepends=True)[27]
        assert "5 / 2" in line
        fixtures.append((line, "#guard (compile pythonSource).isOk"))
    return fixtures, observed


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path)
    args = parser.parse_args()
    assert sys.implementation.name == "cpython", sys.version
    revision = None
    if args.upstream is not None:
        assert sys.version_info[:3] == (3, 13, 5), sys.version
        revision = subprocess.check_output(["git", "-C", str(args.upstream), "rev-parse", "HEAD"], text=True).strip()
        assert revision == QUOTIENT["UPSTREAM"]
    fixtures, observed = controls(args.upstream)
    with tempfile.TemporaryDirectory() as directory:
        source, lean = Path(directory) / "Fixture.py", Path(directory) / "Fixtures.lean"
        INTAKE["check_lean_batch"](source, lean, fixtures, LEAN, extra_imports=SUITE["IMPORTS"])
    print(json.dumps({"cpython": ".".join(map(str, sys.version_info[:3])), "upstream": revision,
                      "cases": observed, "checked_fixtures": len(fixtures)}))
