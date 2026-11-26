# SPDX-License-Identifier: MIT
"""Check the live numeric helper against CPython and replay the isolated pin."""

import argparse
import ast
from contextlib import redirect_stderr, redirect_stdout
import hashlib
from io import StringIO
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
TRANSPORT = runpy.run_path(str(ROOT / "scripts/check-python-division-call-transport.py"))
INTAKE = TRANSPORT["INTAKE"]
QUOTIENT = TRANSPORT["QUOTIENT"]
HELPER = "___assertEqual"
ALIAS = "compare_numbers"
RAISES = "___assertRaises"
FILENAME = "<finite numeric equality>"

LEAN = TRANSPORT["LEAN"] + """
private def equalitySeed (placement : Compile.ModuleEntry.Functions.Run.Seeded.SeedPlacement) : Namespace :=
  let space := Compile.ModuleEntry.Functions.Run.Seeded.legacySeed placement
  { space with builtins := ("compare_numbers", .helper .assertEqual) :: space.builtins }

private def integerTypeSeed (placement : Compile.ModuleEntry.Functions.Run.Seeded.SeedPlacement) : Namespace :=
  let space := Compile.ModuleEntry.Functions.Run.Seeded.legacyTupleIdentitySeed placement
  { space with builtins := [("isinstance", .builtin .isinstance), ("int", .builtin .int)] ++ space.builtins }
"""

PROFILES = (
    ("empty", "Namespace.empty"),
    ("builtin", "(equalitySeed .builtin)"),
    ("preamble", "(equalitySeed .preamble)"),
)

PREFIX = TRANSPORT["PREFIX"]
bits = TRANSPORT["bits"]
lean_value = TRANSPORT["lean_value"]
literal_list = TRANSPORT["literal_list"]
receipt = TRANSPORT["receipt"]
success_receipt = TRANSPORT["success_receipt"]
error_receipt = TRANSPORT["error_receipt"]


def numeric_operand(value):
    if type(value) is int:
        return f".integer ({value})"
    return lean_value(value)


def assertion_error(left, right):
    if type(left) is int and type(right) is int:
        return f".assertionError (.integerPair ({left}) ({right}))"
    return f".assertionError (.numericPair ({numeric_operand(left)}) ({numeric_operand(right)}))"


def cpython(source, profile):
    calls = []

    def equality(name):
        def compare(left, right):
            if left != right:
                calls.append(receipt(name, f".error (.raised ({assertion_error(left, right)}))"))
                raise AssertionError((left, right))
            calls.append(success_receipt(name, None))
        return compare

    compare = equality(HELPER)
    builtins = {}
    namespace = {"__builtins__": builtins}

    def unexpected_expectation(*arguments):
        raise RuntimeError(f"Unexpected exception helper invocation with {arguments!r}")

    if profile in ("builtin", "preamble"):
        builtins[ALIAS] = equality(ALIAS)
        target = builtins if profile == "builtin" else namespace
        target[HELPER] = compare
        target[RAISES] = unexpected_expectation

    def returns(frame, event, value):
        if event == "return" and frame.f_code.co_filename == FILENAME and frame.f_code.co_name == "relay":
            calls.append(success_receipt("relay", value))

    with redirect_stdout(StringIO()) as stdout, redirect_stderr(StringIO()) as stderr:
        profiler = sys.getprofile()
        try:
            sys.setprofile(returns)
            exec(compile(source, FILENAME, "exec", dont_inherit=True, optimize=0), namespace)
            status, error = "normal", None
        except NameError as failure:
            status, error = f"NameError:{failure.name}", f".runtime (.nameError {json.dumps(failure.name)})"
        except ZeroDivisionError:
            status, error = "ZeroDivisionError", ".runtime (.arithmetic .zeroDivisionError)"
        except OverflowError:
            status, error = "OverflowError", ".runtime .overflowError"
        except TypeError:
            status, error = "TypeError", ".runtime .notCallable"
            calls.append(error_receipt(HELPER, ".notCallable"))
        except AssertionError as failure:
            assert len(failure.args) == 1
            status, error = "AssertionError", assertion_error(*failure.args[0])
        finally:
            sys.setprofile(profiler)
    assert stdout.getvalue() == stderr.getvalue() == ""
    assert namespace.pop("__builtins__") is builtins
    if namespace.get(HELPER) is compare:
        del namespace[HELPER]
    if namespace.get(RAISES) is unexpected_expectation:
        del namespace[RAISES]
    return status, error, namespace, calls


def observe(source, expected, lookup_receipts=None):
    writes = {node.id for node in ast.walk(ast.parse(source)) if isinstance(node, ast.Name)
              and isinstance(node.ctx, ast.Store)}
    guards = []
    summary = {}
    for profile, space in (("ordinary", None), *PROFILES):
        status, error, namespace, calls = cpython(source, profile)
        assert status == expected[profile], (profile, status, expected[profile], source)
        values, functions = TRANSPORT["state"](namespace)
        if space is None:
            absent = json.dumps(sorted(writes - namespace.keys()))
            if error is None:
                completion = ".normal"
            else:
                assert error.startswith(".runtime ")
                completion = f".raised {error.removeprefix('.runtime ')}"
            guards.append(TRANSPORT["ordinary"](completion, values, functions, absent))
        else:
            completion = ".ok ()" if error is None else f".error (.raised ({error}))"
            if lookup_receipts is not None and profile in lookup_receipts:
                # The runner also records failed argument calls and failed
                # flat-call preparation, even when CPython enters no callee.
                name = lookup_receipts[profile]
                calls.append(receipt(name, f".error (.raised ({error}))"))
            guards.append(TRANSPORT["seeded"](space, completion, values, functions, literal_list(calls)))
        summary[profile] = {"status": status, "bindings": values, "receipts": calls}
    return (source, "\n".join(guards)), summary


def expect(ordinary, supplied):
    return dict(ordinary=ordinary, empty=ordinary, builtin=supplied, preamble=supplied)


def addition_controls(first):
    operands = []

    def capture(left, right):
        assert type(left) is type(right) is int
        operands.append((left, right))

    exec(compile(first, FILENAME, "exec", dont_inherit=True, optimize=0),
         {"__builtins__": {HELPER: capture}})
    assert operands == [(6, 6)]

    missing = "NameError:___assertEqual"
    fixtures = []
    observations = {}
    for label, source, expected, lookup_receipts in (
        ("isolated integer addition", first, expect(missing, "normal"), {"empty": HELPER}),
        ("signed and large integer addition", PREFIX + "___assertEqual(-7 + 2, -5)\n"
         "___assertEqual((2**53 + 1) + 1, 9007199254740994)\n", expect(missing, "normal"), {"empty": HELPER}),
        ("integer addition mismatch", PREFIX + "___assertEqual(4 + 2, 7)\ntail = 9\n",
         expect(missing, "AssertionError"), {"empty": HELPER}),
        ("integer addition live alias", PREFIX + "___assertEqual = 0\ncompare_numbers(4 + 2, 6)\ntail = 9\n",
         expect("NameError:compare_numbers", "normal"), {"empty": ALIAS}),
        ("integer addition masked callee", PREFIX + "___assertEqual = 0\n___assertEqual(4 + 2, 6)\ntail = 9\n",
         expect("TypeError", "TypeError"), None),
        ("lookup before noncallable mask", PREFIX + "___assertEqual = 0\n___assertEqual(4 + 2, missing)\ntail = 9\n",
         expect("NameError:missing", "NameError:missing"), dict.fromkeys(("empty", "builtin", "preamble"), HELPER)),
        ("reached division after closed sum", PREFIX + "___assertEqual(4 + 2, 1 / 0)\ntail = 9\n",
         expect(missing, "ZeroDivisionError"), None),
    ):
        fixture, observed = observe(source, expected, lookup_receipts)
        fixtures.append(fixture)
        observations[label] = observed

    _, guards = fixtures[0]
    fixtures[0] = (first, guards + """
#guard (match compile pythonSource with
  | .ok compiled => match compiled.instructions with
    | [.call .discard "___assertEqual" [.literal (.int 6), .literal (.int 6)]] => true
    | _ => false
  | .error _ => false)
""")
    observations["isolated integer addition"]["exact_operands"] = operands
    return fixtures, observations


def prefix_control(first_two):
    observed = []
    exec(compile(first_two, FILENAME, "exec", dont_inherit=True, optimize=0),
         {"__builtins__": {HELPER: lambda left, right: observed.append((left, right)),
                          "___assertTrue": observed.append, "isinstance": isinstance, "int": int}})
    assert observed == [(6, 6), True] and type(observed[1]) is bool
    calls = '[("___assertEqual", .ok .none), ("isinstance", .error .unsupported)]'
    guards = [TRANSPORT["seeded"](f"(integerTypeSeed .{placement})", ".error .unsupported", "[]", "[]", calls)
              for placement in ("builtin", "preamble")]
    return (first_two, "\n".join(guards))


def controls(upstream):
    original = "___assertEqual(5 / 2, 2.5)\n"
    first = "___assertEqual(4 + 2, 6)\n"
    full = None
    if upstream is not None:
        raw = (upstream / QUOTIENT["PIN"]).read_bytes()
        assert hashlib.sha256(raw).hexdigest() == QUOTIENT["SHA256"]
        full = raw.decode("utf-8")
        assert full.splitlines(keepends=True)[27] == original
        first_line = full.splitlines(keepends=True)[0]
        assert first_line == first
        first = first_line
    missing = "NameError:___assertEqual"
    through_literal = (
        "def relay(value):\n    return value\n"
        "lower = relay(1.00000000000000011102230246251565404236316680908203125)\n"
        "upper = relay(1.00000000000000033306690738754696212708950042724609375)\n"
        "decimal = relay(+1_0.0_1E-2)\n"
        "subnormal = relay(5e-324)\n"
        "underflow = relay(-1e-400)\n"
    )
    fixtures, observations = addition_controls(first)
    for label, source, expected in (
        ("isolated pin", original, expect(missing, "normal")),
        ("signed zeros", PREFIX + "positive = relay(+0.0)\nnegative = relay(-0.0)\n"
         "___assertEqual(positive, -0.0)\n___assertEqual(negative, 0)\ntail = 9\n", expect(missing, "normal")),
        ("mixed equal", "___assertEqual(9_007_199_254_740_992, 9007199254740993.0)\n", expect(missing, "normal")),
        ("mixed unequal", PREFIX + "___assertEqual(9007199254740993, 9007199254740993.0)\ntail = 9\n",
         expect(missing, "AssertionError")),
        ("mixed unequal reversed", PREFIX + "___assertEqual(9007199254740993.0, 9007199254740993)\ntail = 9\n",
         expect(missing, "AssertionError")),
        ("decimal rounding", through_literal, expect("normal", "normal")),
        ("alias", PREFIX + "___assertEqual = 0\ncompare_numbers(5 / 2, 2.5)\ntail = 9\n",
         expect("NameError:compare_numbers", "normal")),
        ("mask after operands", PREFIX + "___assertEqual = 0\n___assertEqual(5 / 2, 2.5)\ntail = 9\n",
         expect("TypeError", "TypeError")),
        ("division before mask", PREFIX + "___assertEqual = 0\n___assertEqual(1 / 0, missing)\ntail = 9\n",
         expect("ZeroDivisionError", "ZeroDivisionError")),
        ("callee before operands", PREFIX + "___assertEqual(1 / 0, missing)\ntail = 9\n",
         expect(missing, "ZeroDivisionError")),
        ("left operand before overflow", PREFIX + "___assertEqual(missing, 2**1024 / 1)\ntail = 9\n",
         expect(missing, "NameError:missing")),
        ("left receipt before right error", PREFIX + "___assertEqual(relay(2.5), missing)\ntail = 9\n",
         expect(missing, "NameError:missing")),
    ):
        fixture, observed = observe(source, expected)
        fixtures.append(fixture)
        observations[label] = observed

    rounding = cpython(through_literal, "ordinary")[2]
    expected_bits = {
        "lower": "3ff0000000000000", "upper": "3ff0000000000002",
        "decimal": "3fb9a027525460aa", "subnormal": "0000000000000001",
        "underflow": "8000000000000000",
    }
    assert {name: bits(value) for name, value in rounding.items() if name in expected_bits} == expected_bits
    rejected = """#guard (match compile pythonSource with
  | .error (.source (.scalar .expressionProfile)) => true
  | _ => false)"""
    fixtures.extend((source, rejected) for source in (
        "___assertEqual(1e999, 1e999)\n",
        "___assertEqual(1e-4097, 0.0)\n",
    ))
    if full is not None:
        lines = full.splitlines(keepends=True)
        fixtures.append((full, rejected))
        fixtures.append(prefix_control("".join(lines[:2])))
        assert lines[2] == "___assertEqual(4 + 2.0, 6.0)\n"
        assert lines[6] == "___assertEqual(4.0 + 2.0, 6.0)\n"
        fixtures.append(("".join(lines[:6]), "#guard (compile pythonSource).isOk"))
        fixtures.append(("".join(lines[:7]), rejected))
        observations["first prefix cutoffs"] = {
            "first_rejected_compiler_prefix": 7,
            "source": lines[6].rstrip("\n"),
            "seeded_runtime_line": 2,
            "seeded_runtime_cutoff": "unsupported isinstance(int, int)",
        }
        corpus = (upstream / QUOTIENT["PIN"]).parents[1]
        for path, sha256, expected, lookup_receipts in (
            ("bool/bool-float.py", "bca49382b43b0ca3ad600b9d195c5f8154669091727817fc167b202493a24493",
             expect(missing, "NameError:float"), {"builtin": "float", "preamble": "float"}),
            ("range/range-errs.py", "3400b79aec6986e9475b09030c712a3ceb155192ab5960ee4d5eebc8f0dff921",
             expect("NameError:___assertRaises", "NameError:TypeError"), dict.fromkeys(
                 ("empty", "builtin", "preamble"), RAISES)),
        ):
            raw = (corpus / path).read_bytes()
            assert hashlib.sha256(raw).hexdigest() == sha256
            fixture, observed = observe(raw.decode("utf-8"), expected, lookup_receipts)
            fixtures.append(fixture)
            observations[path] = observed
    return fixtures, observations, expected_bits


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path)
    args = parser.parse_args()
    assert sys.implementation.name == "cpython", sys.version
    revision = None
    if args.upstream is not None:
        assert sys.version_info[:3] == (3, 13, 5), sys.version
        revision = subprocess.check_output(["git", "-C", str(args.upstream), "rev-parse", "HEAD"], text=True).strip()
        assert revision == QUOTIENT["UPSTREAM"]
    fixtures, observed, rounded_bits = controls(args.upstream)
    with tempfile.TemporaryDirectory() as directory:
        source, lean = Path(directory) / "Fixture.py", Path(directory) / "Fixtures.lean"
        INTAKE["check_lean_batch"](source, lean, fixtures, LEAN, extra_imports=TRANSPORT["SUITE"]["IMPORTS"])
    print(json.dumps({"cpython": ".".join(map(str, sys.version_info[:3])), "upstream": revision,
                      "fixtures": len(fixtures), "decimal_bits": rounded_bits, "observations": observed}))
