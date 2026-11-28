# SPDX-License-Identifier: MIT
"""Replay checked closed numeric call arguments against CPython 3.13.5."""

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
SUITE = runpy.run_path(str(TESTS / "source-module-entry/check_seeded_run.py"))
INTAKE = runpy.run_path(str(TESTS / "source-scope/check_intake.py"))
PINS = (
    ("bool/bool-compare.py", "628a693566ac2933b3af681985818d49e2202db264c47c073d942aea8dee64f5",
     "___assertIs", "legacy_bool_callable"),
    ("types/bitwise_test.py", "f8b53608c3edb7ec7ed80997feea8bb9f784d2d8c6870549d309e3ec711e74a0",
     "___assertEqual", "legacy"),
)

LEAN = SUITE["LEAN"] + """
private def argumentHeap : Core.Closure.Heap :=
  ⟨1, fun address => if address = 0 then some (.int 23) else none⟩

private def literalArgument : Core.Module.Functions.Operand → Option Value
  | .literal (.int value) => some (.int value)
  | .literal (.bool value) => some (.bool value)
  | _ => none

private def literalCalls (source : Source.Module) : Option (List (String × List Value)) := do
  let compiled ← (Compile.ModuleEntry.Functions.Run.compile source).toOption
  compiled.instructions.mapM fun
    | .call .discard name operands => (operands.mapM literalArgument).map (name, ·)
    | _ => none

private def seededArguments (source : Source.Module) (space : Namespace) (status : String)
    (bindings : Bindings) (receipts : List (String × Result)) : Bool := Id.run do
  let .ok compiled := Compile.ModuleEntry.Functions.Run.compile source | return false
  let lists : Core.Module.ListHeap := ⟨#[[.int 31]]⟩
  let result := Compile.ModuleEntry.Functions.Run.Seeded.run space compiled argumentHeap (lists := lists)
  let completion := match result.completion with
    | .ok () => "normal"
    | .error (.raised error) => raised error
    | .error .unsupported => "unsupported"
    | .error _ => "unexpected completion"
  return completion == status && result.residual.moduleGlobals == bindings &&
    result.residual.builtins == space.builtins && result.lists == lists && result.heap.next == 1 &&
    (result.heap.contents 0).map Compile.ModuleEntry.Functions.Run.Seeded.seededValue == some (.int 23) &&
    result.calls.map (fun call => (call.callee, call.observation.result)) == receipts &&
    result.calls.all (fun call => call.observation.caught.isNone)

private def ordinaryArguments (source : Source.Module) (status : String)
    (bindings : List (String × Option Value)) : Bool := Id.run do
  let .ok compiled := Compile.ModuleEntry.Functions.Run.compile source | return false
  let session := Compile.ModuleEntry.Functions.Run.seed .empty argumentHeap
  let (_, final) := Compile.ModuleEntry.Functions.Run.runPrefix compiled.table 1000
    (.ready session compiled.instructions)
  let .finished residual completion := final | return false
  let observed := match completion with
    | .normal => "normal"
    | .raised error => raised (.runtime error)
    | _ => "unexpected completion"
  return observed == status && residual.heap.next == 1 &&
    (residual.heap.contents 0).map Compile.ModuleEntry.Functions.Run.Seeded.seededValue == some (.int 23) &&
    bindings.all (fun (name, value) => (residual.globals name).map
      Compile.ModuleEntry.Functions.Run.Seeded.seededValue == value)
"""

REJECTED = """#guard (
  match Compile.ModuleEntry.Functions.Run.compile pythonSource with
  | .error (.source (.scalar .expressionProfile)) => true
  | _ => false)"""


def lean_value(value):
    if type(value) is bool:
        return ".bool " + str(value).lower()
    assert type(value) is int
    return f".int ({value})"


def check(source, paths, *guards):
    source_path, lean_path = paths
    INTAKE["emit"](source_path, lean_path, source)
    INTAKE["check_lean"](lean_path, LEAN + "\n".join(guards), extra_imports=SUITE["IMPORTS"])


def cpython(source, bindings, initial=None):
    namespace = dict(initial or {}, __builtins__=bindings)
    with redirect_stdout(StringIO()) as stdout, redirect_stderr(StringIO()) as stderr:
        try:
            exec(compile(source, "<numeric arguments>", "exec", dont_inherit=True, optimize=0), namespace)
            status = "normal"
        except (NameError, TypeError, AssertionError) as error:
            status = SUITE["exception_observation"](error)
        except ValueError:
            status = "ValueError"
    assert not stdout.getvalue() and not stderr.getvalue()
    assert namespace.pop("__builtins__") is bindings
    return status, namespace


def receipt(name, result):
    return f"({json.dumps(name)}, {result})"


def receipts(name, result, count=1):
    return "[" + ", ".join([receipt(name, result)] * count) + "]"


def seeded(space, status, bindings, calls):
    return f"#guard seededArguments pythonSource {space} {json.dumps(status)} {bindings} {calls}"


def literal_guard(name, values):
    calls = [receipt(name, "[" + ", ".join(map(lean_value, args)) + "]") for args in values]
    return "#guard literalCalls pythonSource == some [" + ", ".join(calls) + "]"


def replay(checkout, paths):
    helper_globals = {}
    preamble = runpy.run_path(str(checkout / "tests/python/evaluation/programs.py"))["LAMBDA_PY_PREAMBLE"]
    exec(compile(preamble, "<archived helpers>", "exec", optimize=0), helper_globals)
    observations = {}
    for relative, digest, name, profile in PINS:
        path = "tests/python/programs/original/lambda-py/python-reference/" + relative
        source = SUITE["pinned_source"](checkout, path, digest)
        expected = f"NameError:{name}"
        observed = []

        def record(*args):
            observed.append(args)
            return helper_globals[name](*args)

        assert cpython(source, {}) == (expected, {})
        assert cpython(source, {name: record}) == ("normal", {})
        values = [tuple(eval(compile(ast.Expression(arg), path, "eval", optimize=0), {"__builtins__": {}})
                        for arg in statement.value.args) for statement in ast.parse(source).body]
        assert len(observed) == len(values)
        assert [[(type(value), value) for value in args] for args in observed] == [
            [(type(value), value) for value in args] for args in values]
        assert all(type(value) is (bool if name == "___assertIs" else int)
                   for args in values for value in args)
        missing = receipts(name, f".error (.raised (.runtime (.nameError {json.dumps(name)})))")
        guards = [literal_guard(name, values), seeded("Namespace.empty", expected, "[]", missing),
                  f"#guard ordinaryArguments pythonSource {json.dumps(expected)} []"]
        for placement in ("builtin", "preamble"):
            seed_name = f"{profile}_{placement}"
            space = f"(initial {json.dumps(seed_name)})"
            assert SUITE["cpython"](source, seed_name, expected_globals={}) == ["normal", "absent", "absent"]
            guards.append(seeded(space, "normal", f"{space}.moduleGlobals", receipts(name, ".ok .none", len(values))))
        check(source, paths, *guards)
        observations[relative] = {"sha256": digest, "arguments": observed, "stock_receipts": len(values),
                                  "empty_and_ordinary": expected}
    return observations


def controls(paths):
    name = "___assertEqual"
    stock = '(initial "legacy_builtin")'

    def assert_equal(left, right):
        assert left == right, (left, right)

    compare = {name: assert_equal}
    pairs = ((-5, -9), (-5, 9), (5, -9), (5, 9), (-(2**140), (2**120) + 5))
    expressions = [f"({left}) {operator} ({right})" for operator in ("&", "|", "^")
                   for left, right in pairs]
    expressions += ["(-5) >> 1", "(-5) << 3", "(-5) >> 0", "(-5) >> (2 << 12)",
                    "~((-5) ^ 9)", "1 << 4096"]
    values = [eval(expr, {"__builtins__": {}}) for expr in expressions]
    source = "".join(f"{name}({expr}, {value})\n" for expr, value in zip(expressions, values, strict=True))
    assert cpython(source, compare) == ("normal", {})
    check(source, paths, literal_guard(name, [(value, value) for value in values]),
          seeded(stock, "normal", "[]", receipts(name, ".ok .none", len(values))))

    for prelude, right, profile, status, lean_error in (
        ("", "missing_right", "Namespace.empty", f"NameError:{name}",
         f'.runtime (.nameError "{name}")'),
        (f"{name} = None\n", "missing_right", stock, "NameError:missing_right",
         '.runtime (.nameError "missing_right")'),
        (f"{name} = None\n", "7", stock, "TypeError", ".runtime .notCallable"),
        ("", "8", stock, "AssertionError:pair:7:8", ".assertionError (.integerPair 7 8)"),
    ):
        source = f"keep = 5\n{prelude}{name}(5 | 2, {right})\ntail = 9\n"
        expected = {"keep": 5, **({name: None} if prelude else {})}
        initial = {} if profile == "Namespace.empty" else compare
        assert cpython(source, initial) == (status, expected)
        bindings = f'[("{name}", .none), ("keep", .int 5)]' if prelude else '[("keep", .int 5)]'
        guards = [seeded(profile, status, bindings, receipts(name, f".error (.raised ({lean_error}))"))]
        if prelude or profile == "Namespace.empty":
            mask = "some .none" if prelude else "none"
            ordinary = f'[("keep", some (.int 5)), ("tail", none), ("{name}", {mask})]'
            guards.append(f"#guard ordinaryArguments pythonSource {json.dumps(status)} {ordinary}")
        check(source, paths, *guards)

    source = f"{name} = len\n{name}(5 | 2, 7)\n"
    assert cpython(source, {name: compare[name], "len": len}) == ("TypeError", {name: len})
    space = '(initial "legacy_bool_callable_builtin")'
    check(source, paths, seeded(space, "unsupported", f'[("{name}", .builtin .len)]',
                                receipts(name, ".error .unsupported")))

    source = f"saved = {name}\n{name} = None\n{name} = saved\n{name}(5 | 2, 7)\n"
    assert cpython(source, compare) == ("normal", {name: assert_equal, "saved": assert_equal})
    check(source, paths, seeded(stock, "normal",
                                f'[("{name}", .helper .assertEqual), ("saved", .helper .assertEqual)]',
                                receipts(name, ".ok .none")))

    source = f"{name}(int(False < 1), 1)\n"
    assert cpython(source, compare | {"int": int}) == ("normal", {})
    nested_calls = "[" + receipt("int", ".ok (.int 1)") + ", " + receipt(name, ".ok .none") + "]"
    check(source, paths, seeded('(initial "legacy_bool_int_builtin")', "normal", "[]", nested_calls))

    source = "def verify(value):\n    assert value == 7\nverify(5 | 2)\n"
    status, bindings = cpython(source, {})
    assert status == "normal" and list(bindings) == ["verify"]
    check(source, paths, '#guard ordinaryArguments pythonSource "normal" []')

    for expr, completion in (("1 << -1", "ValueError"), ("1 >> -1", "ValueError"),
                             ("missing & 2", "NameError:missing"), ("True & True", "normal"),
                             ("1 << 4097", "normal")):
        source = f"{name}({expr}, {expr})\n"
        assert cpython(source, compare) == (completion, {})
        check(source, paths, REJECTED)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path, required=True)
    args = parser.parse_args()
    assert sys.version_info[:3] == (3, 13, 5), sys.version
    revision = subprocess.check_output(["git", "-C", str(args.upstream), "rev-parse", "HEAD"], text=True).strip()
    assert revision == SUITE["UPSTREAM_REVISION"], revision
    with tempfile.TemporaryDirectory() as directory:
        source_path = Path(directory) / "Fixture.py"
        paths = (source_path, source_path.with_suffix(".lean"))
        pins = replay(args.upstream, paths)
        controls(paths)
    print(json.dumps({"cpython": sys.version.split()[0], "upstream": revision, "pins": pins,
                      "evaluation_order_and_signed_controls": "passed"}))
