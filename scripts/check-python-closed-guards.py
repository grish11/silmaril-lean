# SPDX-License-Identifier: MIT
"""Replay checked module guards against CPython 3.13.5."""

import argparse
import ast
from contextlib import redirect_stderr, redirect_stdout
from io import StringIO
import json
from pathlib import Path
import runpy
import struct
import subprocess
import sys
import tempfile
import warnings

TESTS = Path(__file__).resolve().parents[1] / "tests/languages/python"
SUITE = runpy.run_path(str(TESTS / "source-module-entry/check_seeded_run.py"))
INTAKE = runpy.run_path(str(TESTS / "source-scope/check_intake.py"))
PIN_DIRECTORY = "tests/python/programs/original/lambda-py/python-reference/types"
PINS = {
    "test_booleans.py": "f97680d3d0948c268714c23fd5ca9decdf543215b511a96f2423ebae4c59f033",
    "test_comparisons.py": "181bf26457c988542c8ebddca3f702d8155844c954a33f6a28102f19940303f5",
    "test_floats.py": "542adfd37c7603f9d3a6eed1db110317d343077f1e94f671c7d88de05c7df1a0",
    "types_truthy1.py": "7f336f91ab2d495e50fda286bf18744ae86d8eb02eccd9dc25fffcf5ec1da70e",
}
SLICE_PIN = "test_string_slices.py"
SLICE_SHA = "91c68c8b2c75f4caf9df187217c98faa4e9ad1ba9e96d1acaee87726497b203c"
PROFILES = ("empty", "legacy_builtin", "legacy_preamble", *SUITE["OPT_IN_PROFILES"])
IMPORTS = (*SUITE["IMPORTS"],
           "meta import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.ClosedGuard.Defs",
           "meta import Silmaril.Languages.Python.Core.Text.Slice.Defs")
LEAN = SUITE["LEAN"] + """
open Compile.ModuleEntry.Functions.ClosedGuard (omitted?)

private def tag : Compile.ModuleEntry.Functions.ClosedGuard.Value → String
  | .scalar (.int value) => s!"int:{value}"
  | .scalar (.bool value) => s!"bool:{value}"
  | .scalar .none => "none"
  | .float value => s!"float:{value.val.bits.toNat}"
  | .text points => "text:" ++ reprStr (points.map UInt32.toNat)
  | .dictionary nonempty => s!"dict:{nonempty}"

private def guardValues (source : Source.Module) : List (Option (Bool × String)) :=
  (source.body.filter fun
    | .if_ .. => true
    | _ => false).map fun statement =>
      (omitted? statement).map fun checked => (checked.val.truth, tag checked.val)

private def guardHeap : Core.Closure.Heap :=
  ⟨1, fun address => if address = 0 then some (.int 23) else none⟩

private def retained (heap : Core.Closure.Heap) : Bool :=
  heap.next == 1 &&
    (heap.contents 0).map Compile.ModuleEntry.Functions.Run.Seeded.seededValue == some (.int 23)

private def noInstructions (source : Source.Module) : Bool :=
  match Compile.ModuleEntry.Functions.Run.compile source with
  | .ok compiled => compiled.instructions.isEmpty && compiled.linked.isEmpty
  | .error _ => false

private def guardError : Raised → String
  | .runtime .zeroSliceStep => "ValueError:slice step cannot be zero"
  | error => raised error

private def ordinaryGuard (source : Source.Module) (status : String)
    (bindings : List (String × Option Value)) : Bool := Id.run do
  let .ok compiled := Compile.ModuleEntry.Functions.Run.compile source | return false
  let lists : Core.Module.ListHeap := ⟨#[[.int 31]]⟩
  let session := { Compile.ModuleEntry.Functions.Run.seed .empty guardHeap with lists := lists }
  let (events, final) := Compile.ModuleEntry.Functions.Run.runPrefix compiled.table 1000
    (.ready session compiled.instructions)
  let .finished residual completion := final | return false
  let observed := match completion with
    | .normal => "normal"
    | .raised error => guardError (.runtime error)
    | .scalarProfile => "unsupported"
    | _ => "unexpected completion"
  return observed == status && retained residual.heap && residual.lists == lists && events.isEmpty &&
    bindings.all (fun (name, value) => (residual.globals name).map
      Compile.ModuleEntry.Functions.Run.Seeded.seededValue == value)

private def seededGuard (source : Source.Module) (profile : String) (status : String)
    (bindings : Bindings) : Bool := Id.run do
  let .ok compiled := Compile.ModuleEntry.Functions.Run.compile source | return false
  let space := initial profile
  let lists : Core.Module.ListHeap := ⟨#[[.int 31]]⟩
  let outcome := Compile.ModuleEntry.Functions.Run.Seeded.run space compiled guardHeap (lists := lists)
  let completion := match outcome.completion with
    | .ok () => "normal"
    | .error (.raised error) => guardError error
    | .error .unsupported => "unsupported"
    | .error _ => "unexpected completion"
  return completion == status && outcome.residual.moduleGlobals == bindings ++ space.moduleGlobals &&
    outcome.residual.builtins == space.builtins && outcome.lists == lists &&
    retained outcome.heap && outcome.calls.isEmpty

private def rejected (source : Source.Module) : Bool :=
  match Compile.ModuleEntry.Functions.Run.compile source with
  | .error (.source (.scalar .statementProfile)) => true
  | _ => false
"""


def cpython(source, builtins=None, globals_=None):
    bindings = {} if builtins is None else builtins
    namespace = {**(globals_ or {}), "__builtins__": bindings}
    stdout, stderr = StringIO(), StringIO()
    with redirect_stdout(stdout), redirect_stderr(stderr):
        try:
            exec(compile(source, "<guard fixture>", "exec", dont_inherit=True, optimize=0), namespace)
            status = "normal"
        except NameError as error:
            status = f"NameError:{error.name}"
        except ZeroDivisionError:
            status = "ZeroDivisionError"
        except ValueError as error:
            status = f"ValueError:{error}"
    assert not stdout.getvalue() and not stderr.getvalue()
    assert namespace.pop("__builtins__") is bindings
    return status, namespace


def value_tag(value):
    if type(value) is bool:
        return "bool:" + str(value).lower()
    if type(value) is int:
        return f"int:{value}"
    if type(value) is float:
        return f"float:{struct.unpack('>Q', struct.pack('>d', value))[0]}"
    if type(value) is str:
        return "text:" + str(list(map(ord, value)))
    if type(value) is dict:
        return "dict:" + str(bool(value)).lower()
    assert value is None
    return "none"


def observations(source):
    return [
        (bool(value), value_tag(value))
        for statement in ast.parse(source).body if isinstance(statement, ast.If)
        for value in [eval(compile(ast.Expression(statement.test), "<test>", "eval", optimize=0),
                          {"__builtins__": {}})]
    ]


def guard_values(values):
    rendered = ", ".join(f"some ({str(truth).lower()}, {json.dumps(tag)})" for truth, tag in values)
    return f"#guard guardValues pythonSource == [{rendered}]"


def check(source, paths, *guards):
    path, lean = paths
    INTAKE["emit"](path, lean, source)
    INTAKE["check_lean"](lean, LEAN + "\n".join(guards), extra_imports=IMPORTS)


def replay(checkout, paths):
    results = {}
    for name, digest in PINS.items():
        source = SUITE["pinned_source"](checkout, f"{PIN_DIRECTORY}/{name}", digest)
        assert cpython(source) == ("normal", {})
        observed = observations(source)
        guards = [guard_values(observed), "#guard noInstructions pythonSource",
                  '#guard ordinaryGuard pythonSource "normal" []']
        for profile in PROFILES:
            assert SUITE["cpython"](source, profile, expected_globals={}) == ["normal", "absent", "absent"]
            guards.append(f'#guard seededGuard pythonSource {json.dumps(profile)} "normal" []')
        check(source, paths, *guards)
        results[name] = {"sha256": digest, "guards": observed, "seeded_placements": len(PROFILES),
                         "receipts": 0}
    return results


def slice_replay(checkout, paths):
    source = SUITE["pinned_source"](checkout, f"{PIN_DIRECTORY}/{SLICE_PIN}", SLICE_SHA)
    parsed = ast.parse(source)
    assert len(parsed.body) == 9 and parsed.body[1].lineno == 2
    assert parsed.body[1].end_lineno == 2
    prefix = "".join(source.splitlines(keepends=True)[:2])
    expected = {"a": "0123456789"}
    guards = []
    for suffix, text in (("throughLineTwo", prefix), ("pythonSource", source)):
        assert cpython(text) == ("normal", expected)
        assert cpython(text, {"Exception": Exception}) == ("normal", expected)
        value = f".text (Core.Text.ofString {json.dumps(expected['a'])})"
        guards.append(f'#guard ordinaryGuard {suffix} "normal" [("a", some ({value}))]')
        for profile in PROFILES:
            assert SUITE["cpython"](text, profile, expected_globals=expected) == ["normal", "absent", "absent"]
            guards.append(f'#guard seededGuard {suffix} {json.dumps(profile)} "normal" [("a", {value})]')
    check(source, paths, "private def throughLineTwo : Source.Module := ⟨pythonSource.body.take 2⟩", *guards)
    return {"sha256": SLICE_SHA, "guards": len(parsed.body) - 1,
            "ordinary_and_seeded": "normal", "receipts": 0}


def slice_controls(paths):
    def points(text):
        return str(list(map(ord, text)))

    def optional(value):
        return "none" if value is None else f"(some ({value}))"

    value = "Aé😀e\u0301\ud800Z"
    guard_terms = []
    for start, stop, step in (
        (None, None, None), (None, None, 2), (1, None, 2),
        (None, None, -1), (None, None, -2), (3, None, -2),
        (-100, 100, None), (100, -100, -1), (-100, 100, 2),
        (None, -1, -1), (None, -8, -1), (-1, None, -1),
        (-100, None, -2), (100, None, 2), (3, 1, 2), (1, 4, -2),
        (-(10**40), 10**40, 10**40), (10**40, -(10**40), -(10**40)),
    ):
        selected = value[slice(start, stop, step)]
        bounds = ", ".join(map(optional, (start, stop, step)))
        guard_terms.append(
            f"#guard ((Core.Text.mk {points(value)} (by decide)).slice? ⟨{bounds}⟩).map "
            f"Core.Text.points == some {points(selected)}"
        )
    for step in (1, -1, 2, -2):
        guard_terms.append(
            f"#guard ((Core.Text.ofString \"\").slice? ⟨none, none, {optional(step)}⟩).map Core.Text.points == some []"
        )
    check("pass\n", paths, *guard_terms)

    fixtures = []
    unicode_slice = f"a = {ascii(value)}\nException = 0\n"
    unicode_slice += f"if not (a[None:None:-2] == {ascii(value[::-2])}): raise Exception('dead')\n"
    unicode_slice += "tail = a\n"
    examples = (
        (unicode_slice, "normal", {"a": value, "Exception": 0, "tail": value}),
        ("a = 'xyz'\nif not (a[::0] == missing): raise Exception('dead')\ntail = 9\n",
         "ValueError:slice step cannot be zero", {"a": "xyz"}),
        ("a = 'xyz'\nif not (missing[::0] == a): raise Exception('dead')\ntail = 9\n",
         "NameError:missing", {"a": "xyz"}),
        ("a = 'xyz'\nif not (missing == a[::0]): raise Exception('dead')\ntail = 9\n",
         "NameError:missing", {"a": "xyz"}),
        ("a = 'xyz'\nif not (a[:] == a[::0]): raise Exception('dead')\ntail = 9\n",
         "ValueError:slice step cannot be zero", {"a": "xyz"}),
        ("a = 'xyz'\nleft = 2\nif not (left == a[::0]): raise Exception('dead')\ntail = 9\n",
         "ValueError:slice step cannot be zero", {"a": "xyz", "left": 2}),
        ("a = 'xyz'\nif not (a[:] == 'bad'): raise Exception('reached')\ntail = 9\n",
         "NameError:Exception", {"a": "xyz"}),
    )

    for source, status, residual in examples:
        assert cpython(source) == (status, residual)
        names = list(reversed(residual))

        def lean(name):
            stored = residual[name]
            return f".text ⟨{points(stored)}, by decide⟩" if type(stored) is str else f".int {stored}"

        seeded = "[" + ", ".join(f'("{name}", {lean(name)})' for name in names) + "]"
        ordinary = "[" + ", ".join(f'("{name}", some ({lean(name)}))' for name in names)
        ordinary += (', ("tail", none)' if "tail" not in residual else "") + "]"
        fixtures.append((source, "\n".join((
            f"#guard ordinaryGuard pythonSource {json.dumps(status)} {ordinary}",
            f'#guard seededGuard pythonSource "legacy_builtin" {json.dumps(status)} {seeded}',
            f'#guard seededGuard pythonSource "legacy_preamble" {json.dumps(status)} {seeded}',
        ))))

    for bound in ("index", "True", "2.0"):
        fixtures.append((f"a = 'xyz'\nindex = 1\nif not (a[::{bound}] == a): raise Exception('bound')\n",
                         "#guard rejected pythonSource"))
    INTAKE["check_lean_batch"](*paths, fixtures, LEAN, extra_imports=IMPORTS)
    return {"code_point_checks": len(guard_terms), "source_controls": len(fixtures),
            "zero_step": "ValueError:slice step cannot be zero"}


def controls(paths):
    source = """keep = 7
Exception = 0
if 0 < ((1 << 2) + 1) < 6 and "𐀀" > "ā": pass
else: raise Exception("comparison")
if 0.1 + 0.2: pass
else: raise Exception("rounding")
if True and -0.0: raise missing("signed zero")
if 5e-324: pass
else: raise missing("subnormal")
if not {"x": 0, "x": False}: raise missing("dictionary")
if {}: raise missing("empty dictionary")
if (False or 5) == 5 and None != 0 and (True is not None): pass
else: raise missing("exact tags")
tail = keep
"""
    assert cpython(source) == ("normal", {"keep": 7, "Exception": 0, "tail": 7})
    observed = observations(source)
    check(source, paths, guard_values(observed),
          '#guard seededGuard pythonSource "legacy_preamble" "normal" '
          '[("tail", .int 7), ("Exception", .int 0), ("keep", .int 7)]',
          '#guard ordinaryGuard pythonSource "normal" '
          '[("tail", some (.int 7)), ("Exception", some (.int 0)), ("keep", some (.int 7))]')

    source = "keep = 7\nif not 1: raise missing('dead')\ntail = missing_right\n"
    assert cpython(source) == ("NameError:missing_right", {"keep": 7})
    check(source, paths,
          '#guard seededGuard pythonSource "legacy_builtin" "NameError:missing_right" [("keep", .int 7)]',
          '#guard ordinaryGuard pythonSource "NameError:missing_right" [("keep", some (.int 7)), ("tail", none)]')

    rejected = "#guard rejected pythonSource"
    for source, status in (
        ("if True: raise missing('reached')\n", "NameError:missing"),
        ("if (1 // 0): raise missing('guard stops first')\n", "ZeroDivisionError"),
        ("if False and (1 >> -1): raise missing('full syntax validation')\n", "normal"),
        ("if 4 < 3 < (1 // 0): raise missing('chain stops')\n", "normal"),
        ("if 1.7976931348623157e308 + 1.7976931348623157e308: pass\nelse: raise missing('finite')\n", "normal"),
        ("if 1 == 1.0: pass\nelse: raise missing('mixed')\n", "normal"),
        ("if False: raise missing(message='dead keyword shape')\n", "normal"),
    ):
        assert cpython(source) == (status, {})
        check(source, paths, rejected)

    events = []

    def probe(value):
        events.append(value)
        return value

    source = "if probe(1) and probe(0) and probe(2): raise missing('unreached')\n"
    assert cpython(source, {"probe": probe}) == ("normal", {}) and events == [1, 0]
    check(source, paths, rejected)

    source = "if ~True: pass\nelse: raise missing('boolean inversion')\n"
    with warnings.catch_warnings(record=True) as emitted:
        warnings.simplefilter("always")
        assert cpython(source) == ("normal", {})
    assert [warning.category for warning in emitted] == [DeprecationWarning]
    check(source, paths, rejected)

    malformed = ast.parse("if True and False: raise Missing\n")
    malformed.body[0].test.values.pop()
    try:
        compile(malformed, "<invalid Boolean arity>", "exec", optimize=0)
    except ValueError:
        pass
    else:
        raise AssertionError("CPython accepted an under-arity Boolean AST")
    check("pass\n", paths,
          '#guard rejected ⟨[.if_ (.booleanOp .and_ [.boolean true]) [.raise_ none none] []]⟩',
          '#guard rejected ⟨[.if_ (.text [0x110000]) [.pass] [.raise_ none none]]⟩')


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path, required=True)
    args = parser.parse_args()
    assert sys.version_info[:3] == (3, 13, 5), sys.version
    revision = subprocess.check_output(["git", "-C", str(args.upstream), "rev-parse", "HEAD"], text=True).strip()
    assert revision == SUITE["UPSTREAM_REVISION"], revision
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "Fixture.py"
        paths = (path, path.with_suffix(".lean"))
        pins = replay(args.upstream, paths)
        controls(paths)
        pins[SLICE_PIN] = slice_replay(args.upstream, paths)
        slices = slice_controls(paths)
    print(json.dumps({"cpython": "3.13.5", "upstream": revision, "pins": pins,
                      "controls": "passed", "text_slices": slices}))
