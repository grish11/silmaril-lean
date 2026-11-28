# SPDX-License-Identifier: MIT
"""Replay live reads of checked dictionary displays against CPython."""

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
PIN = "tests/python/programs/original/lambda-py/python-reference/dict/dict-get.py"
SHA256 = "3ee2c46950b3621e29763f8c5a9ab4e1139b52a2f14213e661040726b4979d02"
FILENAME = "<persistent dictionary>"
PROFILES = {
    "empty": "Namespace.empty",
    **{p: f"(Compile.ModuleEntry.Functions.Run.Seeded.legacyTextSeed .{p})" for p in ("builtin", "preamble")},
}
LEAN = """
open Silmaril.Languages.Python
open Core.Module.SeededCall
open Compile.ModuleEntry.Functions.Run (Completion compile runPrefix seed)

private def initialHeap : Core.Closure.Heap :=
  ⟨1, fun address => if address = 0 then some (.int 23) else none⟩
private def initialLists : Core.Module.ListHeap := ⟨#[[.int 31]]⟩

private def heapMatches (heap : Core.Closure.Heap) (objects : List (Core.Module.Dictionary.Object × List Core.Module.Dictionary.Entry)) : Bool :=
  heap.next == 1 + objects.length && (heap.contents 0).map
    Compile.ModuleEntry.Functions.Run.Seeded.seededValue == some (.int 23) &&
    objects.all fun (object, entries) => heap.dictionaryEntries? object == some entries

private def ordinaryDictionary (source : Source.Module) (completion : Completion)
    (values : Bindings) (absent : List String) (objects : List (Core.Module.Dictionary.Object × List Core.Module.Dictionary.Entry))
    (eventCount : Nat) (clearReturns : Nat := 0) (clearArity : Option Nat := none) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let (events, result) := runPrefix compiled.table 200 (.ready
    { seed .empty initialHeap with lists := initialLists } compiled.instructions)
  let .finished residual reached := result | return false
  let lookup := fun name => (residual.globals name).map Compile.ModuleEntry.Functions.Run.Seeded.seededValue
  let clears := events.filterMap fun
    | .complete (.ok .none) => some (none : Option Nat)
    | .complete (.error (.positionalArity 0 actual)) => some (some actual)
    | _ => none
  let expected := List.replicate clearReturns none ++ clearArity.toList.map some
  return reached == completion && events.length == eventCount && clears == expected &&
    heapMatches residual.heap objects &&
    residual.lists == initialLists && values.all (fun (name, value) => lookup name == some value) &&
    absent.all (fun name => (lookup name).isNone)

private def seededDictionary (source : Source.Module) (space : Namespace)
    (completion : Except Compile.ModuleEntry.Functions.Run.Seeded.ModuleFailure Unit)
    (values : Bindings) (objects : List (Core.Module.Dictionary.Object × List Core.Module.Dictionary.Entry)) (calls : List (String × Result)) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let result := Compile.ModuleEntry.Functions.Run.Seeded.run space compiled initialHeap (lists := initialLists)
  let expected := (values.foldl (fun (base : Namespace) (name, value) =>
    base.bindGlobal name value) space).moduleGlobals
  return result.completion == completion && heapMatches result.heap objects && result.lists == initialLists &&
    result.residual.builtins == space.builtins && result.residual.moduleGlobals.length == expected.length &&
    expected.all (fun (name, value) => lookupBinding result.residual.moduleGlobals name == some value) &&
    result.calls.map (fun call => (call.callee, call.observation.result)) == calls &&
    result.calls.all (fun call => call.observation.caught.isNone)
"""


def atom(value):
    if type(value) is str:
        return f".text ⟨{list(map(ord, value))}, by decide⟩"
    return f".scalar ({scalar(value)})"


def scalar(value):
    if type(value) is bool:
        return f".bool {str(value).lower()}"
    if type(value) is int:
        return f".int ({value})"
    assert value is None
    return ".none"


def entries_term(entries):
    pairs = ", ".join(f"({atom(key)}, {atom(value)})" for key, value in entries.items())
    return f"[{pairs}]"


def object_term(address, entries):
    return f"(⟨{address}⟩, {entries_term(entries)})"


def value_term(value, objects):
    if type(value) is dict:
        position = next(i for i, item in enumerate(objects, start=1) if item is value)
        return f".dictionary ⟨{position}⟩"
    if type(value) is str:
        return atom(value)
    return scalar(value)


def cpython(source, profile, method_events=None):
    objects, helpers, reached_get = [], [], []
    builtins = {}
    namespace = {"__builtins__": builtins}

    def trace(frame, event, arg):
        if frame.f_code.co_filename != FILENAME:
            return None
        if event in ("line", "return"):
            for name, value in frame.f_globals.items():
                if name != "__builtins__" and type(value) is dict and not any(value is other for other in objects):
                    objects.append(value)
        return trace

    def profile_call(frame, event, arg):
        if frame.f_code.co_filename != FILENAME or type(getattr(arg, "__self__", None)) is not dict:
            return
        if event == "c_call" and arg.__name__ == "get":
            reached_get.append(arg.__self__)
        if method_events is not None and arg.__name__ in ("get", "clear") and event in ("c_return", "c_exception"):
            method_events.append((arg.__name__, event))

    def assert_is(left, right):
        assert left is right
        helpers.append(("___assertIs", left))

    def assert_equal(left, right):
        assert type(left) is type(right) and left == right
        helpers.append(("___assertEqual", left))

    def assert_raises(expected, callback, *arguments):
        try:
            callback(*arguments)
        except expected:
            helpers.append(("___assertRaises", expected.__name__))
        else:
            raise AssertionError("expected an exception")

    placement = builtins if profile == "builtin" else namespace
    supplied = {"___assertIs": assert_is, "___assertEqual": assert_equal,
                "___assertRaises": assert_raises, "TypeError": TypeError}
    active = profile in ("builtin", "preamble")
    if active:
        placement.update(supplied)
    with redirect_stdout(StringIO()) as stdout, redirect_stderr(StringIO()) as stderr:
        original_trace, original_profile = sys.gettrace(), sys.getprofile()
        try:
            sys.settrace(trace)
            sys.setprofile(profile_call)
            exec(compile(source, FILENAME, "exec", dont_inherit=True, optimize=0), namespace)
            status = "normal"
        except NameError as error:
            status = f"NameError:{error.name}"
        except AttributeError as error:
            status = f"AttributeError:{error.name}"
        except TypeError as error:
            status = "TypeError"
            if method_events is None:
                raise
            method_events.append(("TypeError", str(error)))
        finally:
            sys.settrace(original_trace)
            sys.setprofile(original_profile)
    assert stdout.getvalue() == stderr.getvalue() == ""
    assert namespace.pop("__builtins__") is builtins
    if active:
        for name, supplied_value in supplied.items():
            assert placement.pop(name) is supplied_value
    return status, namespace, objects, helpers, len(reached_get)


def ok_receipt(name, value, objects):
    return f"({json.dumps(name)}, .ok ({value_term(value, objects)}))"


def case(source, expected, success=(), *, attempted=None, pin=False):
    guards, observed = [], {}
    names = {node.id for node in ast.walk(ast.parse(source))
             if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store)}
    for profile in ("ordinary", *PROFILES):
        status, bindings, objects, helpers, get_count = cpython(source, profile)
        expected_status = ("normal" if profile in ("builtin", "preamble") else "NameError:___assertIs") if pin else expected
        assert status == expected_status, (profile, status, expected_status)
        ledger = "[" + ", ".join(object_term(i, obj) for i, obj in enumerate(objects, start=1)) + "]"
        values = "[" + ", ".join(f"({json.dumps(name)}, {value_term(val, objects)})"
                                  for name, val in bindings.items()) + "]"
        missing = status.removeprefix("NameError:") if status.startswith("NameError:") else None
        outside = status == "AttributeError:get"
        calls = [ok_receipt(receiver + ".get", bindings[name], objects) for receiver, name in success]
        if pin:
            assert not success and get_count == len(helpers)
            for name, value in helpers:
                calls.extend((ok_receipt("d.get", value, objects), ok_receipt(name, None, objects)))
        else:
            assert not helpers and get_count == len(success)
        if attempted:
            failed = f'.raised (.runtime (.nameError {json.dumps(missing)}))' if missing else ".unsupported"
            calls.append(f"({json.dumps(attempted + '.get')}, .error ({failed}))")

        if profile == "ordinary":
            completion = f'.raised (.nameError {json.dumps(missing)})' if missing else (
                ".executorFault .unsupportedDictionaryOperand" if outside else ".normal")
            guards.append(f"#guard ordinaryDictionary pythonSource ({completion}) {values} "
                          f"{json.dumps(sorted(names - bindings.keys()))} {ledger} {int(pin)}")
        else:
            completion = f'.error (.raised (.runtime (.nameError {json.dumps(missing)})))' if missing else (
                ".error .unsupported" if outside else ".ok ()")
            guards.append(f"#guard seededDictionary pythonSource {PROFILES[profile]} ({completion}) {values} "
                          f"{ledger} [{', '.join(calls)}]")
        observed[profile] = {"status": status, "bindings": values, "objects": ledger,
                             "receipts": [] if profile == "ordinary" else calls}
    return (source, "\n".join(guards)), observed


def controls(upstream):
    fixtures, observed = [], {}
    for label, source, status, success, attempted in (
        ("aliases and ordered keys", """
d = {True: 4, 2: 'first', 1: 7, 0: 3, False: None, '\\ud800': 5}
alias = d
fallback = -7
hit = d.get(1, fallback)
miss = alias.get(6, fallback)
null = alias.get(False, 9)
surrogate = alias.get('\\ud800')
d = {'k': 'new'}
other = {'k': 'new'}
after = d.get('k')
retained = alias.get(True)
""", "normal", (("d", "hit"), ("alias", "miss"), ("alias", "null"), ("alias", "surrogate"),
                   ("d", "after"), ("alias", "retained")), None),
        ("default is read on a hit", """
d = {1: 4}
kept = d.get(1)
bad = d.get(1, missing_default)
tail = 9
""", "NameError:missing_default", (("d", "kept"),), "d"),
        ("receiver lookup comes first", "bad = absent.get(missing_key, missing_default)\ntail = 9\n",
         "NameError:absent", (), "absent"),
        ("key lookup before default", "d = {}\nbad = d.get(missing_key, missing_default)\ntail = 9\n",
         "NameError:missing_key", (), "d"),
        ("fallback lookup precedes key type rejection", "d = {}\nkey = {}\nbad = d.get(key, missing_default)\n",
         "NameError:missing_default", (), "d"),
        ("rebound receiver stops before arguments", "d = {}\nalias = d\nd = 7\nbad = d.get(missing_key)\ntail = 9\n",
         "AttributeError:get", (), "d"),
    ):
        fixture, outcome = case(source, status, success, attempted=attempted)
        fixtures.append(fixture)
        observed[label] = outcome
    rejected = "#guard (match compile pythonSource with | .error _ => true | _ => false)"
    fixtures.extend((source, rejected) for source in (
        "d = {1: missing}\n",
        "d = {}; d[1] = 4\n",
        "d = {}; callback = d.get\n",
        "d = {}; found = d.get(1, default=9)\n",
    ))
    if upstream is not None:
        full = SUITE["pinned_source"](upstream, PIN, SHA256)
        lines = full.splitlines(keepends=True)
        assert lines[8] == "___assertRaises(TypeError, d.get)\n"
        fixture, outcome = case("".join(lines[:8]), None, pin=True)
        assert all(len(outcome[profile]["receipts"]) == 12 for profile in ("builtin", "preamble"))
        fixtures.append(fixture)
        fixtures.append((full, """#guard (match compile pythonSource with
  | .error (.source (.scalar .expressionProfile)) => true
  | _ => false)"""))
        assert cpython(full, "builtin")[0] == "normal"
        observed["unchanged pin prefix"] = {"sha256": SHA256, "completed_through": 8, "profiles": outcome,
                                            "next_line": lines[8].rstrip(), "cutoff": "scalar.expressionProfile"}
    return fixtures, observed


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
    fixtures, observed = controls(args.upstream)
    with tempfile.TemporaryDirectory() as directory:
        src, lean = Path(directory) / "Fixture.py", Path(directory) / "Fixtures.lean"
        INTAKE["check_lean_batch"](src, lean, fixtures, LEAN, extra_imports=SUITE["IMPORTS"])
    print(json.dumps({"cpython": sys.version.split()[0], "upstream": revision, "fixtures": len(fixtures),
                      "observations": observed}))
