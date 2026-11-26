# SPDX-License-Identifier: MIT
"""Check typed text operands and stock scalar conversion against CPython 3.13.5."""

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
    ("bool/bool-str.py", "953b7f17ee97076cea75ce4dbf44e0f2cbd6a77b77fbdc00b3654046a3ab5968",
     "___assertEqual", "str", "___assertEqual"),
    ("bool/bool-convert.py", "9c2bc851cb0329fa27186c1ea8ba50f68ffecf56d78d23be193ff9aa405ad0a5",
     "___assertIs", "bool", "___assertIs"),
    ("scope/test-builtin-scope.py", "38c403e24659f7a308844c36be63f31c3fe69c92bea937d2b8d524c39ec62cc2",
     "___assertEqual", "str", "bool"),
)
SLICE_PIN = "tests/python/programs/original/lambda-py/python-reference/range/slice1.py"
SLICE_SHA = "e5427b1ec27c809da19d152b88f97a61697287ee7c399333f8f24645fea05d2e"
STOCK = "(legacyTextSeed .builtin)"

LEAN = SUITE["LEAN"] + """
open Compile.ModuleEntry.Functions.Run.Seeded (legacyTextSeed)

private def textHeap : Core.Closure.Heap :=
  ⟨1, fun address => if address = 0 then some (.int 23) else none⟩

private def retainedTextHeap (heap : Core.Closure.Heap) : Bool :=
  heap.next == 1 &&
    (heap.contents 0).map Compile.ModuleEntry.Functions.Run.Seeded.seededValue == some (.int 23)

private def textOutcome (source : Source.Module) (space : Namespace)
    (completion : Except Compile.ModuleEntry.Functions.Run.Seeded.ModuleFailure Unit)
    (bindings : Bindings) (receipts : List (String × Result)) : Bool := Id.run do
  let .ok compiled := Compile.ModuleEntry.Functions.Run.compile source | return false
  let lists : Core.Module.ListHeap := ⟨#[[.int 31]]⟩
  let outcome := Compile.ModuleEntry.Functions.Run.Seeded.run space compiled textHeap (lists := lists)
  return outcome.completion == completion && outcome.residual.moduleGlobals == bindings &&
    outcome.residual.builtins == space.builtins && outcome.lists == lists &&
    retainedTextHeap outcome.heap &&
    outcome.calls.map (fun call => (call.callee, call.observation.result)) == receipts &&
    outcome.calls.all (fun call => call.observation.caught.isNone)

private def ordinaryText (source : Source.Module) (completion : Compile.ModuleEntry.Functions.Run.Completion)
    (bindings : List (String × Option Value)) : Bool := Id.run do
  let .ok compiled := Compile.ModuleEntry.Functions.Run.compile source | return false
  let lists : Core.Module.ListHeap := ⟨#[[.int 31]]⟩
  let session := { Compile.ModuleEntry.Functions.Run.seed .empty textHeap with lists := lists }
  let (_, final) := Compile.ModuleEntry.Functions.Run.runPrefix compiled.table 1000
    (.ready session compiled.instructions)
  let .finished residual observed := final | return false
  return observed == completion && retainedTextHeap residual.heap && residual.lists == lists &&
    bindings.all (fun (name, value) => (residual.globals name).map
      Compile.ModuleEntry.Functions.Run.Seeded.seededValue == value)
private def sliceValues (source : Source.Module) (space : Namespace) : Option (List Value) := do
  let compiled ← (Compile.ModuleEntry.Functions.Run.compile source).toOption
  let context : Compile.ModuleEntry.Functions.Run.Seeded.CallContext :=
    { table := compiled.table, heap := textHeap, fuel := 1000 }
  compiled.instructions.mapM fun
    | .nestedCall .discard "___assertEqual" arguments =>
      match Compile.ModuleEntry.Functions.Run.Seeded.observeArgumentsIn space context arguments with
      | (.ok [left, _], [], heap) => if retainedTextHeap heap then some left else none
      | _ => none
    | _ => none

"""


def check(source, paths, *guards):
    path, lean = paths
    INTAKE["emit"](path, lean, source)
    INTAKE["check_lean"](lean, LEAN + "\n".join(guards), extra_imports=SUITE["IMPORTS"])


def cpython(source, builtins, initial=None):
    namespace = dict(initial or {}, __builtins__=builtins)
    stdout, stderr = StringIO(), StringIO()
    argument = None
    with redirect_stdout(stdout), redirect_stderr(stderr):
        try:
            unit = compile(source, "<text conversion>", "exec", dont_inherit=True, optimize=0)
            exec(unit, namespace)
            status = "normal"
        except NameError as error:
            status = f"NameError:{error.name}"
        except (TypeError, ValueError) as error:
            status = type(error).__name__
        except AssertionError as error:
            status = "AssertionError"
            (argument,) = error.args
    assert not stdout.getvalue() and not stderr.getvalue()
    assert namespace.pop("__builtins__") is builtins
    return status, namespace, argument


def lean_text(value):
    if value.isascii() and all(32 <= ord(point) < 127 for point in value):
        return f"(Core.Text.ofString {json.dumps(value)})"
    return "⟨" + str(list(map(ord, value))) + ", by decide⟩"


def lean_value(value):
    if type(value) is str:
        return ".text " + lean_text(value)
    if type(value) is int:
        return f".int ({value})"
    if type(value) is bool:
        return ".bool " + str(value).lower()
    assert value is None
    return ".none"


def named(name):
    return f'.runtime (.nameError {json.dumps(name)})'


def calls(*entries):
    return "[" + ", ".join(f"({json.dumps(name)}, {result})" for name, result in entries) + "]"


def outcome(space, completion, bindings, receipts):
    return f"#guard textOutcome pythonSource {space} ({completion}) {bindings} {receipts}"


def ordinary(completion, bindings="[]"):
    return f"#guard ordinaryText pythonSource ({completion}) {bindings}"


def replay(checkout, paths, helpers):
    pins = {}
    for relative, digest, outer, inner, missing in PINS:
        path = "tests/python/programs/original/lambda-py/python-reference/" + relative
        source = SUITE["pinned_source"](checkout, path, digest)
        assert cpython(source, {}) == (f"NameError:{missing}", {}, None)
        builtins = {"str": str, "bool": bool}
        module_bindings = {"int": bool} if missing == "bool" else {}
        trace = []
        for placement in ("builtin", "preamble"):
            fallback = builtins | (helpers if placement == "builtin" else {})
            initial = helpers if placement == "preamble" else {}
            assert cpython(source, fallback, initial) == ("normal", initial | module_bindings, None)
        for statement in ast.parse(source).body:
            if isinstance(statement, ast.Expr):
                call = statement.value.args[0]
                assert isinstance(call, ast.Call) and call.func.id == inner
                trace.append(eval(compile(ast.Expression(call), path, "eval", optimize=0),
                                  {"__builtins__": builtins}))
        assert all(type(value) is (str if inner == "str" else bool) for value in trace)
        receipts = calls(*(entry for value in trace for entry in
                           ((inner, f".ok ({lean_value(value)})"), (outer, ".ok .none"))))
        prefix = '[("int", .builtin .bool)]' if module_bindings else "[]"
        guards = [ordinary(f'.raised (.nameError "{missing}")'),
                  outcome("Namespace.empty", f".error (.raised ({named(missing)}))", "[]", "[]")]
        for placement in ("builtin", "preamble"):
            space = f"(legacyTextSeed .{placement})"
            guards.append(outcome(space, ".ok ()", f"({prefix} ++ {space}.moduleGlobals)", receipts))
        check(source, paths, *guards)
        pins[relative] = {"sha256": digest, "values": trace, "receipts": 2 * len(trace),
                          "empty_and_ordinary": f"NameError:{missing}"}
    return pins


def replay_slice_operands(checkout, paths, helpers):
    source = SUITE["pinned_source"](checkout, SLICE_PIN, SLICE_SHA)
    assert len(ast.parse(source).body) == 7
    assert cpython(source, {}) == ("NameError:___assertEqual", {}, None)
    expected = ["foobar", "foobar", "foobar", "", "raboo", "raboo", "raboof"]
    name = "___assertEqual"
    missing = f".error (.raised ({named(name)}))"
    guards = [ordinary(f'.raised (.nameError "{name}")'), outcome("Namespace.empty", missing, "[]", "[]")]
    for placement in ("builtin", "preamble"):
        trace = []

        def observe(left, right):
            result = helpers[name](left, right)
            assert type(left) is type(right) is str and result is None
            trace.append(left)

        supplied = {name: observe}
        builtins, initial = (supplied, {}) if placement == "builtin" else ({}, supplied)
        assert cpython(source, builtins, initial) == ("normal", initial, None)
        assert trace == expected
        seed = f'(initial "legacy_{placement}")'
        values = "[" + ", ".join(map(lean_value, trace)) + "]"
        guards.extend((
            f"#guard sliceValues pythonSource {seed} == some {values}",
            outcome(seed, ".ok ()", f"{seed}.moduleGlobals", calls(*([(name, ".ok .none")] * len(trace)))),
        ))
    check(source, paths, *guards)
    return {"sha256": SLICE_SHA, "results": expected, "receipts": len(expected),
            "ordinary_and_empty": "NameError:___assertEqual"}


def slice_operand_controls(paths, helpers):
    name = "___assertEqual"
    stock = {"str": str, **helpers}
    value = "é😀e\u0301\ud800"
    target = value[::-2]
    literal = ascii(value)
    error = ".error (.raised (.runtime .zeroSliceStep))"
    residual = '[("keep", .int 7)]'
    mask_residual = '[("___assertEqual", .int 0), ("keep", .int 7)]'
    no_calls = "[]"

    fixtures = []

    def fixture(source, *guards):
        fixtures.append((source, "\n".join(guards)))

    source = f"saved = {name}\n{name} = 0\nsaved({literal}[None:None:-2], {ascii(target)})\n"
    assert cpython(source, stock) == ("normal", {"saved": helpers[name], name: 0}, None)
    fixture(source, outcome(STOCK, ".ok ()", '[("___assertEqual", .int 0), ("saved", .helper .assertEqual)]',
                            calls(("saved", ".ok .none"))))

    source = f"{name}({literal}[::-2], 'different')\n"
    assert cpython(source, stock) == ("AssertionError", {}, (target, "different"))
    mismatch = f".error (.raised (.assertionError (.textPair {lean_text(target)} {lean_text('different')})))"
    fixture(source, outcome(STOCK, mismatch, "[]", calls((name, mismatch))))

    body = f"{name}('x'[::0], missing_right)\ntail = 9\n"
    source = "keep = 7\n" + body
    assert cpython(source, {}) == ("NameError:___assertEqual", {"keep": 7}, None)
    assert cpython(source, stock) == ("ValueError", {"keep": 7}, None)
    fixture(source,
            ordinary('.raised (.nameError "___assertEqual")', '[("keep", some (.int 7)), ("tail", none)]'),
            outcome("Namespace.empty", f".error (.raised ({named(name)}))", residual, no_calls),
            outcome(STOCK, error, residual, no_calls))

    source = f"keep = 7\n{name} = 0\n" + body
    assert cpython(source, stock) == ("ValueError", {"keep": 7, name: 0}, None)
    fixture(source, ordinary(".raised .zeroSliceStep", '[("keep", some (.int 7)), ("tail", none)]'),
            outcome(STOCK, error, mask_residual, no_calls))

    source = f"keep = 7\n{name}(missing_left, 'x'[::0])\ntail = 9\n"
    assert cpython(source, stock) == ("NameError:missing_left", {"keep": 7}, None)
    fixture(source, outcome(STOCK, f".error (.raised ({named('missing_left')}))", residual, no_calls))

    source = f"keep = 7\n{name}(str(False), 'x'[::0])\ntail = 9\n"
    assert cpython(source, stock) == ("ValueError", {"keep": 7}, None)
    fixture(source, outcome(STOCK, error, residual, calls(("str", f".ok ({lean_value('False')})"))))

    source = f"keep = 7\n{name} = 0\n{name}('ab'[::-1], 'ba')\ntail = 9\n"
    not_callable = ".error (.raised (.runtime .notCallable))"
    assert cpython(source, stock) == ("TypeError", {"keep": 7, name: 0}, None)
    fixture(source, ordinary(".raised .notCallable", '[("keep", some (.int 7)), ("tail", none)]'),
            outcome(STOCK, not_callable, mask_residual, calls((name, not_callable))))

    source = f"def consume(value):\n    assert value\nconsume({literal}[::-2])\n"
    status, bindings, argument = cpython(source, {})
    assert status == "normal" and list(bindings) == ["consume"] and argument is None
    fixture(source, ordinary(".normal"))

    INTAKE["check_lean_batch"](*paths, fixtures, LEAN, extra_imports=SUITE["IMPORTS"])
    return {"fixtures": len(fixtures), "exact_code_points": list(map(ord, target)),
            "precedence": True, "retained_inner_receipt": True}


def controls(paths, helpers):
    stock = {"str": str, "bool": bool, **helpers}
    name = "___assertEqual"
    name_error = lambda name: f".error (.raised ({named(name)}))"
    source = "keep = 7\n___assertEqual(str(missing_left), missing_right)\ntail = 9\n"
    assert cpython(source, {}) == ("NameError:___assertEqual", {"keep": 7}, None)
    assert cpython(source, helpers) == ("NameError:str", {"keep": 7}, None)
    assert cpython(source, stock) == ("NameError:missing_left", {"keep": 7}, None)
    check(source, paths,
          ordinary('.raised (.nameError "___assertEqual")', '[("keep", some (.int 7)), ("tail", none)]'),
          outcome("Namespace.empty", name_error(name), '[("keep", .int 7)]', "[]"),
          outcome('(initial "legacy_builtin")', name_error("str"), '[("keep", .int 7)]',
                  calls(("str", name_error("str")))),
          outcome(STOCK, name_error("missing_left"), '[("keep", .int 7)]',
                  calls(("str", name_error("missing_left")))))

    source = "keep = 7\nstr = 0\n___assertEqual(str(missing_left), missing_right)\ntail = 9\n"
    assert cpython(source, stock) == ("NameError:missing_left", {"keep": 7, "str": 0}, None)
    check(source, paths, outcome(STOCK, name_error("missing_left"), '[("str", .int 0), ("keep", .int 7)]',
                                  calls(("str", name_error("missing_left")))))

    source = "keep = 7\n___assertEqual(str(-17), missing_right)\ntail = 9\n"
    assert cpython(source, stock) == ("NameError:missing_right", {"keep": 7}, None)
    text = lean_value("-17")
    check(source, paths, outcome(STOCK, name_error("missing_right"), '[("keep", .int 7)]',
                                  calls(("str", f".ok ({text})"))))
    source = "keep = 7\n___assertEqual(str(-17), '17')\ntail = 9\n"
    assert cpython(source, stock) == ("AssertionError", {"keep": 7}, ("-17", "17"))
    mismatch = f".error (.raised (.assertionError (.textPair {lean_text('-17')} {lean_text('17')})))"
    check(source, paths, outcome(STOCK, mismatch, '[("keep", .int 7)]',
                                  calls(("str", f".ok ({text})"), (name, mismatch))))

    source = "saved = str\nstr = None\nstr = saved\nresult = str(-17)\n___assertEqual(result, '-17')\n"
    assert cpython(source, stock) == ("normal", {"result": "-17", "str": str, "saved": str}, None)
    check(source, paths, outcome(STOCK, ".ok ()",
                                f'[("result", {text}), ("str", .builtin .str), ("saved", .builtin .str)]',
                                calls(("str", f".ok ({text})"), (name, ".ok .none"))))

    source = "___assertEqual(str('\\ud800\\0🧪'), '\\ud800\\0🧪')\n___assertIs(bool('\\0'), True)\n"
    observed = "\ud800\0🧪"
    assert cpython(source, stock) == ("normal", {}, None)
    check(source, paths, outcome(STOCK, ".ok ()", "[]",
                                calls(("str", f".ok ({lean_value(observed)})"), (name, ".ok .none"),
                                      ("bool", ".ok (.bool true)"), ("___assertIs", ".ok .none"))))

    source = "str = 0\nstr('text')\ntail = 9\n"
    assert cpython(source, stock) == ("TypeError", {"str": 0}, None)
    error = ".error (.raised (.runtime .notCallable))"
    check(source, paths, ordinary(".raised .notCallable", '[("str", some (.int 0)), ("tail", none)]'),
          outcome(STOCK, error, '[("str", .int 0)]', calls(("str", error))))

    source = "result = str(False)\nresult(missing)\n"
    assert cpython(source, stock) == ("NameError:missing", {"result": "False"}, None)
    text = lean_value("False")
    check(source, paths, outcome(STOCK, name_error("missing"), f'[("result", {text})]',
                                  calls(("str", f".ok ({text})"), ("result", name_error("missing")))))

    source = "def verify(value):\n    assert value\nverify('text')\n"
    status, bindings, argument = cpython(source, {})
    assert status == "normal" and list(bindings) == ["verify"] and argument is None
    check(source, paths, ordinary(".normal"))

    source = "result = str(value)\n"
    assert sys.int_info.str_digits_check_threshold == 640
    previous = sys.get_int_max_str_digits()
    try:
        sys.set_int_max_str_digits(640)
        small, large = 10**639, 10**640
        rendered = "1" + "0" * 639
        assert cpython(source, stock, {"value": small}) == ("normal", {"value": small, "result": rendered}, None)
        assert cpython(source, stock, {"value": large}) == ("ValueError", {"value": large}, None)
    finally:
        sys.set_int_max_str_digits(previous)
    text = "(.text (Core.Text.ofString (String.ofList ('1' :: List.replicate 639 '0'))))"
    small_space = f'({STOCK}.bindGlobal "value" (.int (10 ^ 639)))'
    large_space = f'({STOCK}.bindGlobal "value" (.int (10 ^ 640)))'
    check(source, paths,
          outcome(small_space, ".ok ()", f'[("result", {text}), ("value", .int (10 ^ 639))]',
                  calls(("str", f".ok {text}"))),
          outcome(large_space, ".error .unsupported", '[("value", .int (10 ^ 640))]',
                  calls(("str", ".error .unsupported"))))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path, required=True)
    args = parser.parse_args()
    assert sys.version_info[:3] == (3, 13, 5), sys.version
    revision = subprocess.check_output(["git", "-C", str(args.upstream), "rev-parse", "HEAD"], text=True).strip()
    assert revision == SUITE["UPSTREAM_REVISION"], revision
    preamble = runpy.run_path(str(args.upstream / "tests/python/evaluation/programs.py"))["LAMBDA_PY_PREAMBLE"]
    namespace = {}
    exec(compile(preamble, "<pinned helpers>", "exec", optimize=0), namespace)
    helpers = {name: namespace[name] for name in ("___assertEqual", "___assertIs")}
    with tempfile.TemporaryDirectory() as directory:
        source = Path(directory) / "Fixture.py"
        paths = (source, source.with_suffix(".lean"))
        pins = replay(args.upstream, paths, helpers)
        controls(paths, helpers)
        pins["range/slice1.py"] = replay_slice_operands(args.upstream, paths, helpers)
        slices = slice_operand_controls(paths, helpers)
    print(json.dumps({"cpython": "3.13.5", "upstream": revision, "pins": pins, "controls": "passed",
                      "slice_operands": slices}))
