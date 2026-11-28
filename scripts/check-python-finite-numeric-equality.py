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
TRUTH = "___assertTrue"
FILENAME = "<finite numeric equality>"

LEAN = TRANSPORT["LEAN"] + """
private def equalitySeed (placement : Compile.ModuleEntry.Functions.Run.Seeded.SeedPlacement) : Namespace :=
  let space := Compile.ModuleEntry.Functions.Run.Seeded.legacySeed placement
  { space with builtins := ("compare_numbers", .helper .assertEqual) :: space.builtins }

private def integerTypeSeed (placement : Compile.ModuleEntry.Functions.Run.Seeded.SeedPlacement) : Namespace :=
  let space := Compile.ModuleEntry.Functions.Run.Seeded.legacyTupleIdentitySeed placement
  { space with builtins := [("isinstance", .builtin .isinstance), ("int", .builtin .int),
    ("bool", .builtin .bool)] ++ space.builtins }
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

def numeric_tag(value):
    assert type(value) in (int, bool, float)
    return f"float64:{bits(value)}" if type(value) is float else f"{type(value).__name__}:{value}"


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


def observe(source, expected, lookup_receipts=None, profiles=PROFILES):
    writes = {node.id for node in ast.walk(ast.parse(source)) if isinstance(node, ast.Name)
              and isinstance(node.ctx, ast.Store)}
    guards = []
    summary = {}
    for profile, space in (("ordinary", None), *profiles):
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


def instance_case(source, expected, probes, *, failed_call=None, probe_name="isinstance", truth_name=TRUTH,
                  numeric=False, unsupported_class=False):
    guards = []
    observed = {}
    for placement in ("builtin", "preamble"):
        calls = []
        tested = []
        compared = []

        def assert_equal(left, right):
            assert left == right and type(left) is type(right)
            compared.append((numeric_tag(left), numeric_tag(right)))
            calls.append(success_receipt(HELPER, None))

        def probe(value, classinfo):
            result = isinstance(value, classinfo)
            assert any(classinfo is kind for kind in (int, bool, float))
            tested.append((numeric_tag(value), classinfo.__name__, result))
            calls.append(receipt(probe_name, f".ok (.bool {str(result).lower()})"))
            return result

        def assert_true(value):
            assert type(value) is bool
            if not value:
                calls.append(receipt(truth_name, ".error (.raised (.assertionError (.boolean false)))"))
                raise AssertionError(value)
            calls.append(success_receipt(truth_name, None))

        builtins = {"isinstance": probe, "int": int, "bool": bool}
        if numeric:
            builtins["float"] = float
        namespace = {"__builtins__": builtins}
        helpers = builtins if placement == "builtin" else namespace
        helpers.update({HELPER: assert_equal, TRUTH: assert_true})
        with redirect_stdout(StringIO()) as stdout, redirect_stderr(StringIO()) as stderr:
            try:
                exec(compile(source, FILENAME, "exec", dont_inherit=True, optimize=0), namespace)
                status, error = "normal", None
            except NameError as failure:
                status, error = f"NameError:{failure.name}", f".runtime (.nameError {json.dumps(failure.name)})"
            except ZeroDivisionError:
                status, error = "ZeroDivisionError", ".runtime (.arithmetic .zeroDivisionError)"
            except TypeError:
                status, error = "TypeError", ".runtime .notCallable"
            except AssertionError as failure:
                assert len(failure.args) == 1 and failure.args[0] is False
                status, error = "AssertionError", ".assertionError (.boolean false)"
        assert stdout.getvalue() == stderr.getvalue() == ""
        assert (status, tested) == (expected, probes), (source, placement, status, tested)
        failure = None
        if error is not None:
            failure = ".unsupported" if unsupported_class else f".raised ({error})"
        if failed_call is not None:
            assert failure is not None
            calls.append(receipt(failed_call, f".error ({failure})"))

        assert namespace.pop("__builtins__") is builtins
        for name, helper in ((HELPER, assert_equal), (TRUTH, assert_true)):
            if namespace.get(name) is helper:
                del namespace[name]
        descriptors = {int: ".builtin .int", bool: ".builtin .bool", float: ".builtin .float",
                       probe: ".builtin .isinstance", assert_true: ".helper .assertTrue"}
        bindings = literal_list(f"({json.dumps(name)}, {descriptors[value] if value in descriptors else lean_value(value)})"
                                for name, value in namespace.items())
        completion = ".ok ()" if failure is None else f".error ({failure})"
        seed = "Compile.ModuleEntry.Functions.Run.Seeded.legacyNumericIsinstanceSeed" if numeric else "integerTypeSeed"
        guards.append(TRANSPORT["seeded"](f"({seed} .{placement})", completion, bindings,
                                          "[]", literal_list(calls)))
        observed[placement] = {"status": status, "probes": tested, "compared": compared,
                               "bindings": bindings, "receipts": calls}
        if unsupported_class:
            observed[placement]["lean_status"] = "unsupported"
    return (source, "\n".join(guards)), observed


def instance_controls(lines):
    successful = [("int:6", "int", True)]
    kept = lines[0] + "kept = 7\n"
    default_call = lines[1]
    fixtures = []
    observations = {}
    for label, source, status, probes, options in (
        ("unchanged three-line prefix", "".join(lines[:3]), "normal", successful, {}),
        ("integer seed runtime cutoff", "".join(lines[:4]), "NameError:float", successful, {"failed_call": "isinstance"}),
        ("live aliases", kept + "probe = isinstance\nkind = int\ncheck = ___assertTrue\n"
         "isinstance = 0\nint = bool\n___assertTrue = 0\ncheck(probe(4 + 2, kind))\ntail = 9\n",
         "normal", successful, {"probe_name": "probe", "truth_name": "check"}),
        ("class mask", kept + "int = bool\n" + default_call + "tail = 9\n",
         "AssertionError", [("int:6", "bool", False)], {}),
        ("probe mask", kept + "isinstance = 0\n" + default_call + "tail = 9\n",
         "TypeError", [], {"failed_call": "isinstance"}),
        ("class lookup before callability", kept + "isinstance = 0\n___assertTrue(isinstance(4 + 2, missing_class))\ntail = 9\n",
         "NameError:missing_class", [], {"failed_call": "isinstance"}),
        ("outer mask retains inner success", kept + "___assertTrue = 0\n" + default_call + "tail = 9\n",
         "TypeError", successful, {"failed_call": TRUTH}),
        ("operand order", kept + "___assertTrue(isinstance(missing_value, missing_class))\ntail = 9\n",
         "NameError:missing_value", [], {"failed_call": "isinstance"}),
        ("outer lookup first", kept + "missing_helper(isinstance(missing_value, missing_class))\ntail = 9\n",
         "NameError:missing_helper", [], {}),
    ):
        fixture, observed = instance_case(source, status, probes, **options)
        fixtures.append(fixture)
        observations[label] = observed

    prefix = "".join(lines[:6])
    addition_prefix = "".join(lines[:8])
    subtraction_prefix = "".join(lines[:17])
    multiplication_prefix = "".join(lines[:29])
    division_prefix = "".join(lines[:35])
    floor_prefix = "".join(lines[:38])
    fixed = (
        PROFILES[0],
        *((placement, f"(Compile.ModuleEntry.Functions.Run.Seeded.legacyTextSeed .{placement})")
          for placement in ("builtin", "preamble")),
    )
    fixture, observed = observe(division_prefix, expect("NameError:___assertEqual", "NameError:___assertTrue"),
                                {"empty": HELPER}, profiles=fixed)
    fixtures.append(fixture)
    observations["thirty-five-line prefix in fixed profiles"] = observed
    fixture, observed = observe(floor_prefix, expect("NameError:___assertEqual", "NameError:___assertTrue"),
                                {"empty": HELPER}, profiles=fixed)
    fixtures.append(fixture)
    observations["thirty-eight-line prefix in fixed profiles"] = observed

    mixed = "float64:4018000000000000"
    for label, source, status, probes, options in (
        ("unchanged six-line numeric prefix", prefix, "normal",
         successful + [(mixed, "float", True), (mixed, "float", True)], {}),
        ("live float class alias", kept + "kind = float\nfloat = int\n"
         "___assertTrue(isinstance(4 + 2.0, kind))\ntail = 9\n", "normal", [(mixed, "float", True)], {}),
        ("float class masked by int", kept + "float = int\n" + lines[3] + "tail = 9\n",
         "AssertionError", [(mixed, "int", False)], {}),
        ("float class masked by bool", kept + "float = bool\n" + lines[3] + "tail = 9\n",
         "AssertionError", [(mixed, "bool", False)], {}),
        ("nonclass float mask", kept + "float = 0\n" + lines[3] + "tail = 9\n",
         "TypeError", [], {"failed_call": "isinstance", "unsupported_class": True}),
        ("int tested with the float class", kept + "___assertTrue(isinstance(6, float))\ntail = 9\n",
         "AssertionError", [("int:6", "float", False)], {}),
        ("bool tested with the float class", kept + "___assertTrue(isinstance(True, float))\ntail = 9\n",
         "AssertionError", [("bool:True", "float", False)], {}),
        ("zero and subnormal float instances", kept + "___assertTrue(isinstance(-0.0, float))\n"
         "___assertTrue(isinstance(5e-324, float))\n", "normal",
         [("float64:8000000000000000", "float", True), ("float64:0000000000000001", "float", True)], {}),
        ("float instance receipt before outer mask", kept + "___assertTrue = 0\n" + lines[3] + "tail = 9\n",
         "TypeError", [(mixed, "float", True)], {"failed_call": TRUTH}),
        ("arithmetic error before class lookup and callability", kept + "isinstance = 0\n"
         "___assertTrue(isinstance(1 / 0, missing_class))\ntail = 9\n",
         "ZeroDivisionError", [], {"failed_call": "isinstance"}),
        ("inner lookup before arithmetic", kept + "___assertTrue(missing_probe(1 / 0, float))\ntail = 9\n",
         "NameError:missing_probe", [], {"failed_call": "missing_probe"}),
    ):
        fixture, observed = instance_case(source, status, probes, numeric=True, **options)
        fixtures.append(fixture)
        observations[label] = observed

    (source, guards), observed = instance_case(addition_prefix, "normal",
                                               successful + [(mixed, "float", True)] * 3, numeric=True)
    assert all(profile["compared"] == [("int:6", "int:6")] + [(mixed, mixed)] * 3
               for profile in observed.values())
    guards += """
#guard (match compile pythonSource with
  | .ok compiled => match compiled.instructions.drop 6 with
    | [.nestedCall .discard "___assertEqual"
         [.scalar (.floatAdd left right), .scalar (.literal (.float64 expected))],
       .nestedCall .discard "___assertTrue" [.call "isinstance" [.floatAdd first second, .readGlobal "float"]]] =>
      left.val.bits == 0x4010000000000000 && right.val.bits == 0x4000000000000000 &&
        first.val.bits == left.val.bits && second.val.bits == right.val.bits &&
        expected.val.bits == 0x4018000000000000 &&
        (Core.Binary64.addFinite? left right).map (fun result => result.val.bits) == some expected.val.bits
    | _ => false
  | _ => false)
"""
    fixtures.append((source, guards))
    observations["unchanged eight-line numeric prefix"] = observed

    difference = "float64:4000000000000000"
    probes = successful + [(mixed, "float", True)] * 3
    probes += [("int:2", "int", True)] + [(difference, "float", True)] * 3
    (source, guards), observed = instance_case(subtraction_prefix, "normal", probes, numeric=True)
    comparisons = [("int:6", "int:6")] + [(mixed, mixed)] * 3
    comparisons += [("int:2", "int:2")] + [(difference, difference)] * 3
    assert all(profile["compared"] == comparisons for profile in observed.values())
    guards += """
#guard (match compile pythonSource with
  | .ok compiled => match compiled.instructions.drop 8 with
    | [.call .discard "___assertEqual" [.literal (.int 2), .literal (.int 2)], _,
       .nestedCall .discard "___assertEqual" [.scalar (.floatSub (.intFloat 4 rhs)), _], _,
       .nestedCall .discard "___assertEqual" [.scalar (.floatSub (.floatInt lhs 2)), _], _,
       .nestedCall .discard "___assertEqual" [.scalar (.floatSub (.floatFloat left right)), _], _] =>
        lhs.val.bits == 0x4010000000000000 && rhs.val.bits == 0x4000000000000000 &&
          left.val.bits == lhs.val.bits && right.val.bits == rhs.val.bits
    | _ => false
  | _ => false)
"""
    fixtures.append((source, guards))
    observations["unchanged seventeen-line numeric prefix"] = observed

    product = "float64:4020000000000000"
    quotient = "float64:4004000000000000"
    probes += [("int:8", "int", True)] + [(product, "float", True)] * 3 + [(quotient, "float", True)]
    comparisons += [("int:8", "int:8")] + [(product, product)] * 3 + [(quotient, quotient)]
    (source, guards), observed = instance_case(multiplication_prefix, "normal", probes, numeric=True)
    assert all(profile["compared"] == comparisons for profile in observed.values())
    guards += """
#guard (match compile pythonSource with
  | .ok compiled => match compiled.instructions.drop 16 with
    | [.call .discard "___assertEqual" [.literal (.int 8), .literal (.int 8)], _,
       .nestedCall .discard "___assertEqual" [.scalar (.floatMul (.intFloat 4 rhs)), _], _,
       .nestedCall .discard "___assertEqual" [.scalar (.floatMul (.floatInt lhs 2)), _], _,
       .nestedCall .discard "___assertEqual" [.scalar (.floatMul (.floatFloat left right)), _], _, _, _] =>
        lhs.val.bits == 0x4010000000000000 && rhs.val.bits == 0x4000000000000000 &&
          left.val.bits == lhs.val.bits && right.val.bits == rhs.val.bits
    | _ => false
  | _ => false)
"""
    fixtures.append((source, guards))
    observations["unchanged twenty-nine-line numeric prefix"] = observed

    probes += [(quotient, "float", True)] * 3
    comparisons += [(quotient, quotient)] * 3
    (source, guards), observed = instance_case(division_prefix, "normal", probes, numeric=True)
    assert all(profile["compared"] == comparisons for profile in observed.values())
    guards += """
#guard (match compile pythonSource with
  | .ok compiled => match compiled.instructions.drop 26 with
    | [.nestedCall .discard "___assertEqual" [.scalar (.floatDiv (.intFloat 5 rhs)), _], _,
       .nestedCall .discard "___assertEqual" [.scalar (.floatDiv (.floatInt lhs 2)), _], _,
       .nestedCall .discard "___assertEqual" [.scalar (.floatDiv (.floatFloat left right)), _], _] =>
        lhs.val.bits == 0x4014000000000000 && rhs.val.bits == 0x4000000000000000 &&
          left.val.bits == lhs.val.bits && right.val.bits == rhs.val.bits
    | _ => false
  | _ => false)
"""
    fixtures.append((source, guards))
    observations["unchanged thirty-five-line numeric prefix"] = observed
    probes += [("int:2", "int", True)]
    comparisons += [("int:2", "int:2")]
    (source, guards), observed = instance_case(floor_prefix, "normal", probes, numeric=True)
    assert all(profile["compared"] == comparisons and len(profile["receipts"]) == 51
               for profile in observed.values())
    guards += """
#guard (match compile pythonSource with
  | .ok compiled => match compiled.instructions.drop 32 with
    | [.nestedCall .discard "___assertEqual" [.scalar (.intDivMod .floorDiv 5 2), .scalar (.literal (.int 2))],
       .nestedCall .discard "___assertTrue" [.call "isinstance" [.intDivMod .floorDiv 5 2, .readGlobal "int"]]] => true
    | _ => false
  | _ => false)
"""
    fixtures.append((source, guards))
    observations["unchanged thirty-eight-line numeric prefix"] = observed

    source = ""
    comparisons = []
    for numerator, divisor, quotient, remainder in TRANSPORT["INT_DIVMOD_CASES"]:
        for op, result in (("//", quotient), ("%", remainder)):
            source += f"___assertEqual({numerator} {op} {divisor}, {result})\n"
            comparisons.append((f"int:{result}", f"int:{result}"))
    fixture, observed = instance_case(source, "normal", [], numeric=True)
    assert all(profile["compared"] == comparisons and len(profile["receipts"]) == len(comparisons)
               for profile in observed.values())
    fixtures.append(fixture)
    observations["seeded integer floor quotient and remainder"] = observed

    source = ("kept = 7\n___assertEqual(-5 // 2, -3)\n"
              "___assertEqual(isinstance(5 % 2, int), 1 // 0)\ntail = 9\n")
    fixture, observed = instance_case(source, "ZeroDivisionError", [("int:1", "int", True)], numeric=True)
    assert all(profile["compared"] == [("int:-3", "int:-3")] and len(profile["receipts"]) == 2
               for profile in observed.values())
    fixtures.append(fixture)
    observations["integer divmod receipts before late argument error"] = observed
    return fixtures, observations


def controls(upstream):
    original = "___assertEqual(5 / 2, 2.5)\n"
    first = "___assertEqual(4 + 2, 6)\n"
    instance_prefix = [
        first,
        "___assertTrue(isinstance(4 + 2, int))\n",
        "___assertEqual(4 + 2.0, 6.0)\n",
        "___assertTrue(isinstance(4 + 2.0, float))\n",
        "___assertEqual(4.0 + 2, 6.0)\n",
        "___assertTrue(isinstance(4.0 + 2, float))\n",
        "___assertEqual(4.0 + 2.0, 6.0)\n",
        "___assertTrue(isinstance(4.0 + 2.0, float))\n",
        "\n",
        "___assertEqual(4 - 2, 2)\n",
        "___assertTrue(isinstance(4 - 2, int))\n",
        "___assertEqual(4 - 2.0, 2.0)\n",
        "___assertTrue(isinstance(4 - 2.0, float))\n",
        "___assertEqual(4.0 - 2, 2.0)\n",
        "___assertTrue(isinstance(4.0 - 2, float))\n",
        "___assertEqual(4.0 - 2.0, 2.0)\n",
        "___assertTrue(isinstance(4.0 - 2.0, float))\n",
        "\n",
        "___assertEqual(4 * 2, 8)\n",
        "___assertTrue(isinstance(4 * 2, int))\n",
        "___assertEqual(4 * 2.0, 8.0)\n",
        "___assertTrue(isinstance(4 * 2.0, float))\n",
        "___assertEqual(4.0 * 2, 8.0)\n",
        "___assertTrue(isinstance(4.0 * 2, float))\n",
        "___assertEqual(4.0 * 2.0, 8.0)\n",
        "___assertTrue(isinstance(4.0 * 2.0, float))\n",
        "\n",
        original,
        "___assertTrue(isinstance(5 / 2, float))\n",
        "___assertEqual(5 / 2.0, 2.5)\n",
        "___assertTrue(isinstance(5 / 2.0, float))\n",
        "___assertEqual(5.0 / 2, 2.5)\n",
        "___assertTrue(isinstance(5.0 / 2, float))\n",
        "___assertEqual(5.0 / 2.0, 2.5)\n",
        "___assertTrue(isinstance(5.0 / 2.0, float))\n",
        "\n",
        "___assertEqual(5 // 2, 2)\n",
        "___assertTrue(isinstance(5 // 2, int))\n",
    ]
    full = None
    if upstream is not None:
        raw = (upstream / QUOTIENT["PIN"]).read_bytes()
        assert hashlib.sha256(raw).hexdigest() == QUOTIENT["SHA256"]
        full = raw.decode("utf-8")
        assert full.splitlines(keepends=True)[27] == original
        first_line = full.splitlines(keepends=True)[0]
        assert first_line == first
        first = first_line
        assert full.splitlines(keepends=True)[:38] == instance_prefix
        instance_prefix = full.splitlines(keepends=True)[:38]
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
    instance_fixtures, instance_observations = instance_controls(instance_prefix)
    fixtures.extend(instance_fixtures)
    observations.update(instance_observations)
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
        assert lines[2] == "___assertEqual(4 + 2.0, 6.0)\n"
        assert lines[38] == "___assertEqual(5.0 // 2, 2.0)\n"
        assert len(lines) == 53 and lines[-1] == "___assertTrue(isinstance(5.0 % 2.0, float))\n"

        prefix = observations["unchanged thirty-eight-line numeric prefix"]["builtin"]
        extra = [("float64:4000000000000000", "float", True)] * 3
        extra += [("int:1", "int", True)] + [("float64:3ff0000000000000", "float", True)] * 3
        fixture, observed = instance_case(full, "normal", prefix["probes"] + extra, numeric=True)
        expected_comparisons = prefix["compared"] + [(value, value) for value, _, _ in extra]
        assert all(profile["compared"] == expected_comparisons and len(profile["receipts"]) == 72
                   for profile in observed.values())
        source, guards = fixture
        guards += """
#guard (match compile pythonSource with
  | .ok compiled =>
    match (compiled.instructions[34]?, compiled.instructions[46]?) with
    | (some (Compile.ModuleEntry.Functions.Run.Instruction.nestedCall .discard "___assertEqual"
        [.scalar (.floatDivMod .floorDiv (.floatInt lhs 2)), _]),
       some (Compile.ModuleEntry.Functions.Run.Instruction.nestedCall .discard "___assertEqual"
        [.scalar (.floatDivMod .modulo (.floatFloat left right)), _])) =>
        lhs.val.bits == 0x4014000000000000 && left.val.bits == lhs.val.bits &&
          right.val.bits == 0x4000000000000000
    | _ => false
  | _ => false)
"""
        fixtures.append((source, guards))
        observations["unchanged full numeric pin"] = observed

        fixed = (
            PROFILES[0],
            *((placement, f"(Compile.ModuleEntry.Functions.Run.Seeded.legacyTextSeed .{placement})")
              for placement in ("builtin", "preamble")),
        )
        fixture, observed = observe(full, expect(missing, "NameError:___assertTrue"), {"empty": HELPER}, profiles=fixed)
        fixtures.append(fixture)
        observations["full numeric pin in fixed profiles"] = observed
        remainder = "".join(lines[45:47])
        assert remainder == "___assertEqual(5 % 2, 1)\n___assertTrue(isinstance(5 % 2, int))\n"
        fixture, observed = instance_case(remainder, "normal", [("int:1", "int", True)], numeric=True)
        assert all(profile["compared"] == [("int:1", "int:1")] and len(profile["receipts"]) == 3
                   for profile in observed.values())
        fixtures.append(fixture)
        observations["isolated unchanged integer remainder"] = observed
        observations["first prefix cutoffs"] = {
            "first_rejected_compiler_prefix": None,
            "numeric_seed_completed_through": len(lines),
            "integer_seed_runtime_line": 4,
            "integer_seed_runtime_cutoff": "NameError:float",
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
