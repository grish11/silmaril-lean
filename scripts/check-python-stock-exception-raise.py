# SPDX-License-Identifier: MIT
"""Replay the checked stock Exception raise path against CPython 3.13.5."""

import argparse
import ast
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile


NORMAL = runpy.run_path(str(Path(__file__).with_name("check-python-normal-try.py")))
SUITE = NORMAL["SUITE"]
INTAKE = NORMAL["INTAKE"]
LEAN = SUITE["LEAN"] + """
open Compile.ModuleEntry.Functions

private def reachedHeap : Core.Closure.Heap :=
  ⟨1, fun slot => if slot == 0 then some (.int 23) else none⟩

private def reachedLists : Core.Module.ListHeap := ⟨#[[.int 31]]⟩

private def stock : Bindings := [("Exception", .exceptionClass .exception),
  ("___assertTrue", .helper .assertTrue), ("___assertFalse", .helper .assertFalse)]

private def ordinaryRaise (source : Source.Module) (seed expected : Bindings) (status : Run.Completion)
    (events : List Core.Closure.Executor.Event := []) : Bool := Id.run do
  let .ok compiled := Run.compile source | return false
  let lookup name := match lookupBinding seed name with
    | some (.exceptionClass kind) => some (.exceptionClass kind)
    | other => other.bind Run.Seeded.ordinaryValue?
  let initial : Core.Module.Functions.Session := ⟨lookup, reachedHeap, reachedLists⟩
  let (actualEvents, state) := Run.runPrefix compiled.table 1000 (.ready initial compiled.instructions)
  let .finished result completed := state | return false
  let names := (compiled.checked.tree.scope.context.assigned ++ seed.map Prod.fst).eraseDups
  let actual := names.filterMap fun name =>
    (result.globals name).map (fun value => (name, Run.Seeded.seededValue value))
  return completed == status && actual.length == expected.length && expected.all actual.contains &&
    result.heap.next == reachedHeap.next &&
    (result.heap.contents 0).map Run.Seeded.seededValue == some (.int 23) &&
    result.lists == reachedLists &&
    (match actualEvents, events with
      | [], [] => true
      | [.complete (.error actual)], [.complete (.error expected)] => actual == expected
      | _, _ => false)

private def seededRaise (source : Source.Module) (space : Namespace) (expected : Bindings)
    (status : Except Run.Seeded.ModuleFailure Unit) (receipts : List (String × Result)) : Bool := Id.run do
  let .ok compiled := Run.compile source | return false
  let result := Run.Seeded.run space compiled reachedHeap (lists := reachedLists)
  return result.completion == status && result.residual.moduleGlobals.length == expected.length &&
    expected.all result.residual.moduleGlobals.contains && result.residual.builtins == space.builtins &&
    result.heap.next == reachedHeap.next &&
    (result.heap.contents 0).map Run.Seeded.seededValue == some (.int 23) &&
    result.lists == reachedLists && result.calls.all (·.observation.caught.isNone) &&
    result.calls.map (fun call => (call.callee, call.observation.result)) == receipts
"""

PINS = (
    ("try-except-finally.py", "fba8104968df003a261e1f38921768503bf35746ad884bc7a249e0596bd15377", False),
    ("try-except-else-finally.py", "a236fe94cf7db0c0ab1b4ccb01c37443e0c3a9dcb31592273b3ee4ccdd1cadbb", True),
)


def codepoints(text):
    return "[" + ", ".join(str(ord(char)) for char in text) + "]"


STOCK_CLASSES = {
    Exception: "exception", AssertionError: "assertionError", NameError: "nameError",
    UnboundLocalError: "unboundLocalError", TypeError: "typeError", ValueError: "valueError",
    ZeroDivisionError: "zeroDivisionError", OverflowError: "overflowError", RuntimeError: "runtimeError",
}


def instance_code(value):
    if not value.args:
        return f".empty .{STOCK_CLASSES[type(value)]}"
    assert type(value) is Exception and len(value.args) == 1 and type(value.args[0]) is str
    return f".text ⟨{codepoints(value.args[0])}, by decide⟩"


def value_code(value):
    if value in STOCK_CLASSES:
        return ".exceptionClass ." + STOCK_CLASSES[value]
    if type(value) in STOCK_CLASSES:
        return f".exceptionInstance ({instance_code(value)})"
    if type(value) is str:
        return f".text ⟨{codepoints(value)}, by decide⟩"
    if value is None:
        return ".none"
    if type(value) is bool:
        return ".bool " + str(value).lower()
    assert type(value) is int
    return f".int ({value})"


def bindings(values):
    return "[" + ", ".join(f"({json.dumps(name)}, {value_code(value)})" for name, value in values.items()) + "]"


def execute(raw, expected, status, *, seed=None, preamble=False):
    builtins = {} if preamble else (seed or {})
    initial = seed if preamble else {}
    namespace = dict(initial or {}, __builtins__=builtins)
    selected = None
    try:
        exec(compile(raw, "<stock exception raise>", "exec", dont_inherit=True, optimize=0), namespace)
    except NameError as error:
        selected = ("name", error.name)
    except TypeError as error:
        assert error.args == ("'NoneType' object is not callable",)
        selected = ("type", None)
    except Exception as error:
        assert type(error) is Exception and len(error.args) == 1 and type(error.args[0]) is str
        selected = ("exception", error.args[0])
    assert selected == status and namespace.pop("__builtins__") is builtins
    wanted = dict(initial or {}) | expected
    assert namespace.keys() == wanted.keys()
    assert all(type(actual) is type(wanted[key]) and actual == wanted[key] for key, actual in namespace.items())
    for key, value in expected.items():
        if value is Exception:
            assert namespace[key] is Exception


def errors(status):
    if status is None:
        return ".normal", ".ok ()"
    kind, value = status
    if kind == "name":
        error = f".nameError {json.dumps(value)}"
    elif kind == "type":
        error = ".notCallable"
    else:
        assert kind == "exception"
        error = f".explicitException ⟨{codepoints(value)}, by decide⟩"
    return f".raised ({error})", f".error (.raised (.runtime ({error})))"


def control(source, expected, status, *, stock=False):
    seed = {"Exception": Exception} if stock else {}
    execute(source.encode(), expected, status, seed=seed)
    ordinary, seeded = errors(status)
    entries = bindings(expected)
    return source, f"""#guard ordinaryRaise pythonSource {bindings(seed)} {bindings(seed | expected)} ({ordinary})
#guard seededRaise pythonSource ⟨[], {bindings(seed)}⟩ {entries} ({seeded}) []"""


def controls():
    yield control(r'''
kept = Exception
Exception = None
message = "\u00e9\U0001f600\ud800"
try:
    reached = 7
    raise kept(message)
    after_raise = 8
finally:
    cleanup = reached
after_try = 9
''', {"kept": Exception, "Exception": None, "message": "é😀\ud800", "reached": 7, "cleanup": 7},
        ("exception", "é😀\ud800"), stock=True)

    yield control("""
try:
    reached = True
    raise Exception(argument_missing)
finally:
    kept = reached
""", {"reached": True, "kept": True}, ("name", "Exception"))

    yield control("""
Exception = None
try:
    reached = True
    raise Exception(argument_missing)
finally:
    kept = reached
""", {"Exception": None, "reached": True, "kept": True}, ("name", "argument_missing"), stock=True)

    yield control("""
Exception = None
try:
    reached = None
    raise Exception("ignored")
finally:
    kept = reached
""", {"Exception": None, "reached": None, "kept": None}, ("type", None), stock=True)

    yield control("""
try:
    reached = True
    raise Exception("discarded")
finally:
    kept = reached
    late = cleanup_missing
""", {"reached": True, "kept": True}, ("name", "cleanup_missing"), stock=True)


def pins(upstream):
    helper_path = "tests/python/evaluation/programs.py"
    harness = SUITE["pinned_source"](upstream, helper_path,
        "55091465bd9ff2b6f784d31b48798f50dfffb98b712e22c96fe4092b6e4eb37f")
    preamble, = (ast.literal_eval(statement.value) for statement in ast.parse(harness).body
                 if isinstance(statement, ast.Assign) and any(
                     isinstance(target, ast.Name) and target.id == "LAMBDA_PY_PREAMBLE"
                     for target in statement.targets))
    helpers = {}
    exec(compile(preamble, helper_path, "exec", dont_inherit=True, optimize=0), helpers)
    for name, digest, has_else in PINS:
        path = f"{NORMAL['PREFIX']}/{name}"
        source = SUITE["pinned_source"](upstream, path, digest)
        raw = (upstream / path).read_bytes()
        assert source.encode() == raw
        state = {"hit_except": True, "hit_finally": True}
        if has_else:
            state["hit_else"] = False
        execute(raw, state, ("name", "___assertTrue"))
        entries = bindings(state)
        guards = [f'#guard ordinaryRaise pythonSource [] {entries} (.raised (.nameError "___assertTrue")) '
                  '[.complete (.error (.nameError "___assertTrue"))]']
        error = '.error (.raised (.runtime (.nameError "___assertTrue")))'
        for profile in (".empty", 'initial "legacy_builtin"', 'initial "legacy_preamble"'):
            guards.append(f'#guard let space : Namespace := {profile}; seededRaise pythonSource space '
                          f'({entries} ++ space.moduleGlobals) ({error}) [("___assertTrue", {error})]')
        calls = [("___assertTrue", True), ("___assertTrue", True)]
        if has_else:
            calls.append(("___assertFalse", False))
        for use_preamble in (False, True):
            observed = []

            def trace(helper):
                def call(value):
                    assert type(value) is bool
                    result = helpers[helper](value)
                    observed.append((helper, value, result))
                    return result
                return call

            seed = {"Exception": Exception, **{helper: trace(helper) for helper in ("___assertTrue", "___assertFalse")}}
            execute(raw, state, None, seed=seed, preamble=use_preamble)
            assert observed == [(name, value, None) for name, value in calls]
            space, residual = ("⟨stock, []⟩", f"({entries} ++ stock)") if use_preamble else ("⟨[], stock⟩", entries)
            receipts = "[" + ", ".join(f'("{callee}", .ok .none)' for callee, _ in calls) + "]"
            guards.append(f"#guard seededRaise pythonSource {space} {residual} (.ok ()) {receipts}")
        yield source, "\n".join(guards)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path, required=True)
    args = parser.parse_args()
    assert sys.version_info[:3] == (3, 13, 5)
    revision = subprocess.check_output(["git", "-C", str(args.upstream), "rev-parse", "HEAD"], text=True).strip()
    assert revision == SUITE["UPSTREAM_REVISION"]
    unchanged = list(pins(args.upstream))
    reached = list(controls())
    with tempfile.TemporaryDirectory() as scratch:
        source = Path(scratch) / "Fixture.py"
        INTAKE["check_lean_batch"](source, source.with_suffix(".lean"), unchanged + reached, LEAN,
                                   extra_imports=SUITE["IMPORTS"])
    print(json.dumps({"cpython": "3.13.5", "unchanged_pins": len(unchanged), "reached_controls": len(reached)}))
