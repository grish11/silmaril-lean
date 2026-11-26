# SPDX-License-Identifier: MIT
"""Replay checked binary64 call arithmetic against CPython."""

import argparse
import hashlib
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
EQUALITY = runpy.run_path(str(ROOT / "scripts/check-python-finite-numeric-equality.py"))
TRANSPORT = EQUALITY["TRANSPORT"]
QUOTIENT = EQUALITY["QUOTIENT"]
INTAKE = EQUALITY["INTAKE"]
PREFIX = EQUALITY["PREFIX"]
HELPER = EQUALITY["HELPER"]
bits = EQUALITY["bits"]
expect = EQUALITY["expect"]
observe = EQUALITY["observe"]

MAX_FINITE_INTEGER = (2**53 - 1) * 2**971
CONVERSION_MIDPOINT = 2**1024 - 2**970
FLOAT_OVERFLOW = "1.7976931348623157e308 + 9.9792015476736e291"
SUB_OVERFLOW = "1.7976931348623157e308 - -9.9792015476736e291"
MUL_OVERFLOW_LEFT = "1.3407807830046643e154"
MUL_OVERFLOW_RIGHT = "1.340780802983855e154"
MUL_OVERFLOW = f"{MUL_OVERFLOW_LEFT} * {MUL_OVERFLOW_RIGHT}"
DIV_OVERFLOW = "1.7976931348623157e308 / 0.9999999999999999"


def nonfinite_control(expression, expected_bits):
    source = PREFIX + f"bad = relay({expression})\ntail = 9\n"
    status, _, namespace, _ = EQUALITY["cpython"](source, "ordinary")
    assert status == "normal"
    assert bits(namespace.pop("bad")) == expected_bits
    assert namespace.pop("tail") == 9
    values, functions = TRANSPORT["state"](namespace)
    guards = [TRANSPORT["ordinary"](".executorFault .unsupportedFloatOperand", values, functions, '["bad", "tail"]')]
    prior = TRANSPORT["success_receipt"]("relay", namespace["result"])
    guards.extend(TRANSPORT["seeded"](space, ".error .unsupported", values, functions, f"[{prior}]")
                  for _, space in EQUALITY["PROFILES"])
    return (source, "\n".join(guards))


def float_controls():
    cases = {
        "sum": ("4.0 + 2.0", "4018000000000000"),
        "reversed": ("2.0 + 4.0", "4018000000000000"),
        "neg_zeros": ("-0.0 + -0.0", "8000000000000000"),
        "opposite_zeros": ("-0.0 + 0.0", "0000000000000000"),
        "opposite_zeros_reversed": ("0.0 + -0.0", "0000000000000000"),
        "cancellation": ("-4.0 + 4.0", "0000000000000000"),
        "subnormal": ("5e-324 + 5e-324", "0000000000000002"),
        "negative_subnormal": ("-5e-324 + -5e-324", "8000000000000002"),
        "minimum_normal": ("2.225073858507201e-308 + 5e-324", "0010000000000000"),
        "subnormal_difference": ("2.2250738585072014e-308 + -2.225073858507201e-308", "0000000000000001"),
        "lower_tie": ("1.0 + 1.1102230246251565e-16", "3ff0000000000000"),
        "upper_tie": ("3.3306690738754696e-16 + 1.0", "3ff0000000000002"),
        "below_overflow_midpoint": ("1.7976931348623157e308 + 9.979201547673598e291", "7fefffffffffffff"),
    }
    finite = PREFIX + "".join(f"{name} = relay({expression})\n" for name, (expression, _) in cases.items())
    expected_bits = {name: result for name, (_, result) in cases.items()}
    namespace = EQUALITY["cpython"](finite, "ordinary")[2]
    assert {name: bits(namespace[name]) for name in cases} == expected_bits
    fixtures = []
    observations = {}
    missing = "NameError:___assertEqual"
    for label, source, expected in (
        ("float sum bits", finite, expect("normal", "normal")),
        ("left lookup before right float overflow", PREFIX +
         f"___assertEqual(missing, {FLOAT_OVERFLOW})\ntail = 9\n",
         expect(missing, "NameError:missing")),
        ("float sum receipt before right lookup", PREFIX + "___assertEqual(relay(4.0 + 2.0), missing)\ntail = 9\n",
         expect(missing, "NameError:missing")),
        ("float sum before noncallable mask", PREFIX + "___assertEqual = 0\n"
         "___assertEqual(4.0 + 2.0, 6.0)\ntail = 9\n", expect("TypeError", "TypeError")),
        ("float sum mismatch payload", PREFIX + "___assertEqual(4.0 + 2.0, 7.0)\ntail = 9\n",
         expect(missing, "AssertionError")),
    ):
        fixture, observed = observe(source, expected)
        fixtures.append(fixture)
        observations[label] = observed

    fixtures.extend((
        nonfinite_control(FLOAT_OVERFLOW, "7ff0000000000000"),
        nonfinite_control("-1.7976931348623157e308 + -9.9792015476736e291", "fff0000000000000"),
    ))
    return fixtures, observations, expected_bits


def subtraction_controls():
    cases = {
        "mixed_left": ("4 - 2.0", "4000000000000000"),
        "mixed_right": ("2.0 - 4", "c000000000000000"),
        "floats_reversed": ("2.0 - 4.0", "c000000000000000"),
        "integer_left_rounding": ("9007199254740993 - 9007199254740992.0", "0000000000000000"),
        "integer_right_rounding": ("9007199254740992.0 - 9007199254740993", "0000000000000000"),
        "negative_zero": ("-0.0 - 0.0", "8000000000000000"),
        "negative_zero_int": ("-0.0 - 0", "8000000000000000"),
        "subtract_negative_zero": ("0 - -0.0", "0000000000000000"),
        "two_negative_zeros": ("-0.0 - -0.0", "0000000000000000"),
        "subnormal": ("2.2250738585072014e-308 - 2.225073858507201e-308", "0000000000000001"),
        "negative_subnormal": ("5e-324 - 1e-323", "8000000000000001"),
        "lower_tie": ("1.0 - -1.1102230246251565e-16", "3ff0000000000000"),
        "upper_tie": ("1.0 - -3.3306690738754696e-16", "3ff0000000000002"),
        "below_overflow_midpoint": ("1.7976931348623157e308 - -9.979201547673598e291", "7fefffffffffffff"),
        "integer_below_conversion_midpoint": (f"{CONVERSION_MIDPOINT - 1} - 0.0", "7fefffffffffffff"),
    }
    finite = PREFIX + "".join(f"{name} = relay({expression})\n" for name, (expression, _) in cases.items())
    expected_bits = {name: result for name, (_, result) in cases.items()}
    namespace = EQUALITY["cpython"](finite, "ordinary")[2]
    assert {name: bits(namespace[name]) for name in cases} == expected_bits

    missing = "NameError:___assertEqual"
    fixtures = []
    observations = {}
    integer_differences = PREFIX + (
        "___assertEqual(-3 - -2, -1)\n___assertEqual(2 - (3 - 4), 3)\n"
        "___assertEqual((2**1024 - 1) - (2**1024 - 2), 1)\n"
    )
    fixture, observed = observe(integer_differences, expect(missing, "normal"), {"empty": HELPER})
    fixtures.append(fixture)
    observations["exact integer differences"] = observed

    for label, source, expected in (
        ("subtraction bits", finite, expect("normal", "normal")),
        ("left integer conversion overflow", PREFIX +
         f"bad = relay({CONVERSION_MIDPOINT} - 1.7976931348623157e308)\ntail = 9\n",
         expect("OverflowError", "OverflowError")),
        ("right integer conversion overflow", PREFIX +
         f"bad = relay(1.7976931348623157e308 - {CONVERSION_MIDPOINT})\ntail = 9\n",
         expect("OverflowError", "OverflowError")),
        ("subtraction conversion before right lookup and mask", PREFIX + "___assertEqual = 0\n"
         f"___assertEqual(1.0 - {CONVERSION_MIDPOINT}, missing)\ntail = 9\n",
         expect("OverflowError", "OverflowError")),
        ("subtraction operand lookup before noncallable mask", PREFIX + "___assertEqual = 0\n"
         "___assertEqual(4.0 - 2.0, missing)\ntail = 9\n", expect("NameError:missing", "NameError:missing")),
        ("subtraction mask after preparation", PREFIX + "___assertEqual = 0\n"
         "___assertEqual(4.0 - 2.0, 2.0)\ntail = 9\n", expect("TypeError", "TypeError")),
        ("missing callee before subtraction conversion", PREFIX +
         f"___assertEqual({CONVERSION_MIDPOINT} - 1.0, missing)\ntail = 9\n",
         expect(missing, "OverflowError")),
        ("left lookup before right subtraction overflow", PREFIX +
         f"___assertEqual(missing, {SUB_OVERFLOW})\ntail = 9\n", expect(missing, "NameError:missing")),
        ("subtraction receipt before right lookup", PREFIX +
         "___assertEqual(relay(2.0 - 4), missing)\ntail = 9\n", expect(missing, "NameError:missing")),
    ):
        fixture, observed = observe(source, expected)
        fixtures.append(fixture)
        observations[label] = observed

    fixtures.extend((
        nonfinite_control(SUB_OVERFLOW, "7ff0000000000000"),
        nonfinite_control("-1.7976931348623157e308 - 9.9792015476736e291", "fff0000000000000"),
    ))
    return fixtures, observations, expected_bits


def multiplication_controls():
    # The exact product of these binary64 integers is the overflow midpoint.
    assert int(float(MUL_OVERFLOW_LEFT)) * int(float(MUL_OVERFLOW_RIGHT)) == CONVERSION_MIDPOINT
    cases = {
        "mixed_left": ("4 * 2.0", "4020000000000000"),
        "mixed_right": ("2.0 * -4", "c020000000000000"),
        "floats": ("4.0 * 2.0", "4020000000000000"),
        "integer_left_rounding": ("9007199254740993 * 3.0", "4358000000000000"),
        "integer_right_rounding": ("3.0 * 9007199254740993", "4358000000000000"),
        "negative_zero": ("-0.0 * 2.0", "8000000000000000"),
        "positive_zero": ("-0.0 * -2.0", "0000000000000000"),
        "integer_zero_left": ("0 * -2.0", "8000000000000000"),
        "integer_zero_right": ("-2.0 * 0", "8000000000000000"),
        "half_minimum_subnormal": ("5e-324 * 0.5", "0000000000000000"),
        "negative_underflow": ("-5e-324 * 0.5", "8000000000000000"),
        "above_half_minimum_subnormal": ("5e-324 * 0.5000000000000001", "0000000000000001"),
        "subnormal_tie_up": ("5e-324 * 1.5", "0000000000000002"),
        "subnormal_tie_down": ("-5e-324 * 2.5", "8000000000000002"),
        "half_minimum_normal": ("2.2250738585072014e-308 * 0.5", "0008000000000000"),
        "normal_tie_up": ("1.0000000000000002 * 1.5", "3ff8000000000002"),
        "normal_tie_down": ("1.0000000000000007 * 1.5", "3ff8000000000004"),
        "below_overflow_midpoint": (f"1.3407807830046642e154 * {MUL_OVERFLOW_RIGHT}", "7feffffffffffffe"),
    }
    finite = PREFIX + "".join(f"{name} = relay({expression})\n" for name, (expression, _) in cases.items())
    expected_bits = {name: result for name, (_, result) in cases.items()}
    namespace = EQUALITY["cpython"](finite, "ordinary")[2]
    assert {name: bits(namespace[name]) for name in cases} == expected_bits
    assert bits(float(9007199254740993 * 3)) == "4358000000000001"

    missing = "NameError:___assertEqual"
    integer_products = PREFIX + (
        "___assertEqual(-4 * 2, -8)\n___assertEqual((2 - 5) * -3, 9)\n"
        "___assertEqual(2**1024 * 2**1024, 2**2048)\n"
    )
    fixture, observed = observe(integer_products, expect(missing, "normal"), {"empty": HELPER})
    fixtures, observations = [fixture], {"exact integer products": observed}
    for label, source, expected in (
        ("multiplication bits", finite, expect("normal", "normal")),
        ("left integer conversion before zero product", PREFIX +
         f"bad = relay({CONVERSION_MIDPOINT} * 0.0)\ntail = 9\n", expect("OverflowError", "OverflowError")),
        ("right integer conversion before zero product", PREFIX +
         f"bad = relay(0.0 * {CONVERSION_MIDPOINT})\ntail = 9\n", expect("OverflowError", "OverflowError")),
        ("multiplication conversion before right lookup and mask", PREFIX + "___assertEqual = 0\n"
         f"___assertEqual(0.0 * {CONVERSION_MIDPOINT}, missing)\ntail = 9\n",
         expect("OverflowError", "OverflowError")),
        ("multiplication operand lookup before noncallable mask", PREFIX + "___assertEqual = 0\n"
         "___assertEqual(4.0 * 2.0, missing)\ntail = 9\n", expect("NameError:missing", "NameError:missing")),
        ("multiplication mask after preparation", PREFIX + "___assertEqual = 0\n"
         "___assertEqual(4.0 * 2.0, 8.0)\ntail = 9\n", expect("TypeError", "TypeError")),
        ("missing callee before multiplication conversion", PREFIX +
         f"___assertEqual({CONVERSION_MIDPOINT} * 0.0, missing)\ntail = 9\n", expect(missing, "OverflowError")),
        ("left lookup before right product overflow", PREFIX +
         f"___assertEqual(missing, {MUL_OVERFLOW})\ntail = 9\n", expect(missing, "NameError:missing")),
        ("product receipt before right lookup", PREFIX +
         "___assertEqual(relay(2.0 * -4), missing)\ntail = 9\n", expect(missing, "NameError:missing")),
    ):
        fixture, observed = observe(source, expected)
        fixtures.append(fixture)
        observations[label] = observed

    fixtures.extend((
        nonfinite_control(MUL_OVERFLOW, "7ff0000000000000"),
        nonfinite_control(f"-{MUL_OVERFLOW}", "fff0000000000000"),
    ))
    return fixtures, observations, expected_bits


def division_controls():
    cases = {
        "exact_integer_before_numerator_cast": ("9007199254740993 / 3", "4325555555555556"),
        "converted_numerator": ("9007199254740993 / 3.0", "4325555555555555"),
        "exact_integer_before_divisor_cast": ("9007199254740987 / 9007199254740993", "3feffffffffffffa"),
        "converted_divisor": ("9007199254740987.0 / 9007199254740993", "3feffffffffffffb"),
        "huge_integer_ratio": ("2**1024 / 2**1024", "3ff0000000000000"),
        "float_ratio": ("5.0 / -2.0", "c004000000000000"),
        "mixed_zero_numerator": ("0 / -2.0", "8000000000000000"),
        "negative_zero_numerator": ("-0.0 / 2", "8000000000000000"),
        "two_negative_signs": ("-0.0 / -2.0", "0000000000000000"),
        "half_minimum_subnormal": ("5e-324 / 2", "0000000000000000"),
        "negative_underflow": ("-5e-324 / 2.0", "8000000000000000"),
        "above_half_minimum_subnormal": ("5e-324 / 1.9999999999999998", "0000000000000001"),
        "subnormal_tie_up": ("1.5e-323 / 2.0", "0000000000000002"),
        "subnormal_tie_down": ("-2.5e-323 / 2", "8000000000000002"),
        "half_minimum_normal": ("2.2250738585072014e-308 / 2.0", "0008000000000000"),
        "largest_finite": ("1.7976931348623157e308 / 1.0", "7fefffffffffffff"),
    }
    finite = PREFIX + "".join(f"{name} = relay({expression})\n" for name, (expression, _) in cases.items())
    expected_bits = {name: result for name, (_, result) in cases.items()}
    namespace = EQUALITY["cpython"](finite, "ordinary")[2]
    assert {name: bits(namespace[name]) for name in cases} == expected_bits

    missing = "NameError:___assertEqual"
    fixtures, observations = [], {}
    for label, source, expected in (
        ("division bits", finite, expect("normal", "normal")),
        ("cast before positive zero divisor", PREFIX + "bad = relay(2**1024 / 0.0)\ntail = 9\n",
         expect("OverflowError", "OverflowError")),
        ("cast before negative zero divisor", PREFIX + "bad = relay(2**1024 / -0.0)\ntail = 9\n",
         expect("OverflowError", "OverflowError")),
        ("divisor cast with zero numerator", PREFIX + "bad = relay(0.0 / 2**1024)\ntail = 9\n",
         expect("OverflowError", "OverflowError")),
        ("mixed positive zero divisor", PREFIX + "bad = relay(1 / 0.0)\ntail = 9\n",
         expect("ZeroDivisionError", "ZeroDivisionError")),
        ("mixed integer zero divisor", PREFIX + "bad = relay(-0.0 / 0)\ntail = 9\n",
         expect("ZeroDivisionError", "ZeroDivisionError")),
        ("float negative zero divisor", PREFIX + "bad = relay(1.0 / -0.0)\ntail = 9\n",
         expect("ZeroDivisionError", "ZeroDivisionError")),
        ("integer result overflow is defined", PREFIX + "bad = relay(2**1024 / 1)\ntail = 9\n",
         expect("OverflowError", "OverflowError")),
        ("missing callee before division conversion", PREFIX + "___assertEqual(2**1024 / 0.0, missing)\n"
         "tail = 9\n", expect(missing, "OverflowError")),
        ("zero divisor before right lookup and mask", PREFIX + "___assertEqual = 0\n"
         "___assertEqual(1.0 / 0, missing)\ntail = 9\n", expect("ZeroDivisionError", "ZeroDivisionError")),
        ("lookup before right division", PREFIX + "___assertEqual(missing, 1 / 0.0)\ntail = 9\n",
         expect(missing, "NameError:missing")),
        ("quotient receipt before right zero divisor", PREFIX +
         "___assertEqual(relay(-0.0 / 2), 1.0 / -0.0)\ntail = 9\n", expect(missing, "ZeroDivisionError")),
        ("division mask after preparation", PREFIX + "___assertEqual = 0\n"
         "___assertEqual(5 / 2.0, 2.5)\ntail = 9\n", expect("TypeError", "TypeError")),
    ):
        fixture, observed = observe(source, expected)
        fixtures.append(fixture)
        observations[label] = observed

    fixtures.extend((
        nonfinite_control(DIV_OVERFLOW, "7ff0000000000000"),
        nonfinite_control("-2 / 5e-324", "fff0000000000000"),
    ))
    return fixtures, observations, expected_bits


def controls(upstream):
    forward = "___assertEqual(4 + 2.0, 6.0)\n"
    reverse = "___assertEqual(4.0 + 2, 6.0)\n"
    if upstream is not None:
        raw = (upstream / QUOTIENT["PIN"]).read_bytes()
        assert hashlib.sha256(raw).hexdigest() == QUOTIENT["SHA256"]
        lines = raw.decode("utf-8").splitlines(keepends=True)
        assert lines[1] == "___assertTrue(isinstance(4 + 2, int))\n"
        assert lines[2] == forward and lines[4] == reverse
        forward, reverse = lines[2], lines[4]

    for line in (forward, reverse):
        received = []
        exec(compile(line, "<mixed add pin>", "exec", dont_inherit=True, optimize=0),
             {"__builtins__": {HELPER: lambda left, right: received.append((bits(left), bits(right)))}})
        assert received == [("4018000000000000", "4018000000000000")]

    finite = PREFIX + (
        "forward = relay(4 + 2.0)\n"
        "reverse = relay(4.0 + 2)\n"
        "cancellation = relay(9007199254740993 + -9007199254740992.0)\n"
        "cancellation_reversed = relay(-9007199254740992.0 + 9007199254740993)\n"
        "zero = relay(0 + -0.0)\n"
        "zero_reversed = relay(-0.0 + 0)\n"
        "positive_subnormal = relay(0 + 5e-324)\n"
        "negative_subnormal = relay(-5e-324 + 0)\n"
        "lower_tie = relay(1 + 1.1102230246251565e-16)\n"
        "upper_tie = relay(1 + 3.3306690738754696e-16)\n"
        f"at_edge = relay({CONVERSION_MIDPOINT - 1} + 0.0)\n"
    )
    expected_bits = {
        "forward": "4018000000000000", "reverse": "4018000000000000",
        "cancellation": "0000000000000000", "cancellation_reversed": "0000000000000000",
        "zero": "0000000000000000", "zero_reversed": "0000000000000000",
        "positive_subnormal": "0000000000000001", "negative_subnormal": "8000000000000001",
        "lower_tie": "3ff0000000000000", "upper_tie": "3ff0000000000002",
        "at_edge": "7fefffffffffffff",
    }
    namespace = EQUALITY["cpython"](finite, "ordinary")[2]
    assert {name: bits(namespace[name]) for name in expected_bits} == expected_bits

    missing = "NameError:___assertEqual"
    fixtures = []
    observations = {}
    for label, source, expected in (
        ("isolated line 3", forward, expect(missing, "normal")),
        ("isolated line 5", reverse, expect(missing, "normal")),
        ("finite result bits", finite, expect("normal", "normal")),
        ("conversion overflow before cancellation", PREFIX +
         f"bad = relay({CONVERSION_MIDPOINT} + -1.7976931348623157e308)\ntail = 9\n",
         expect("OverflowError", "OverflowError")),
        ("reversed conversion overflow", PREFIX +
         f"bad = relay(0.0 + {CONVERSION_MIDPOINT})\ntail = 9\n", expect("OverflowError", "OverflowError")),
        ("conversion failure before mask", PREFIX +
         "___assertEqual = 0\n___assertEqual(2**1024 + 0.0, missing)\ntail = 9\n",
         expect("OverflowError", "OverflowError")),
        ("mask after successful preparation", PREFIX +
         "___assertEqual = 0\n___assertEqual(4 + 2.0, 6.0)\ntail = 9\n", expect("TypeError", "TypeError")),
        ("missing callee before overflow", PREFIX +
         "___assertEqual(2**1024 + 0.0, missing)\ntail = 9\n", expect(missing, "OverflowError")),
        ("first operand lookup before overflow", PREFIX +
         "___assertEqual(missing, 2**1024 + 0.0)\ntail = 9\n", expect(missing, "NameError:missing")),
        ("inner receipt before overflow", PREFIX +
         "___assertEqual(relay(4 + 2.0), 2**1024 + 0.0)\ntail = 9\n", expect(missing, "OverflowError")),
        ("mixed mismatch payload", PREFIX + "___assertEqual(4 + 2.0, 7.0)\ntail = 9\n",
         expect(missing, "AssertionError")),
    ):
        fixture, observed = observe(source, expected)
        fixtures.append(fixture)
        observations[label] = observed

    fixtures.append(nonfinite_control(f"{MAX_FINITE_INTEGER} + 1.7976931348623157e308", "7ff0000000000000"))
    float_fixtures, float_observations, float_bits = float_controls()
    fixtures.extend(float_fixtures)
    observations.update(float_observations)
    sub_fixtures, sub_observations, sub_bits = subtraction_controls()
    fixtures.extend(sub_fixtures)
    observations.update(sub_observations)
    mul_fixtures, mul_observations, mul_bits = multiplication_controls()
    fixtures.extend(mul_fixtures)
    observations.update(mul_observations)
    div_fixtures, div_observations, div_bits = division_controls()
    fixtures.extend(div_fixtures)
    observations.update(div_observations)
    rejected = """#guard (match compile pythonSource with
  | .error (.source (.scalar .expressionProfile)) => true
  | _ => false)"""
    fixtures.extend((f"relay({expression})\n", rejected) for expression in
                    ("(4 + 2.0) + 1", "(4.0 + 2.0) + 1.0", "4 + 1e999", "4.0 + 1e999", "1e999 + 2.0"))
    for expression in ("None - 2", "1.0 - None", "None * 2", "1.0 * None", "None / 2", "1.0 / None"):
        source = PREFIX + f"relay({expression})\n"
        assert EQUALITY["cpython"](source, "ordinary")[0] == "TypeError"
        fixtures.append((source, rejected))
    fixtures.extend((f"relay({expression})\n", rejected) for expression in
                    ("1e999 - 2.0", "2.0 - 1e999", "1e999 * 2.0", "2.0 * 1e999", "1e999 / 2.0", "2.0 / 1e999"))
    return fixtures, observations, expected_bits, float_bits, sub_bits, mul_bits, div_bits


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
    fixtures, observed, result_bits, float_bits, sub_bits, mul_bits, div_bits = controls(args.upstream)
    with tempfile.TemporaryDirectory() as directory:
        source, lean = Path(directory) / "Fixture.py", Path(directory) / "Fixtures.lean"
        INTAKE["check_lean_batch"](source, lean, fixtures, EQUALITY["LEAN"], extra_imports=TRANSPORT["SUITE"]["IMPORTS"])
    print(json.dumps({"cpython": ".".join(map(str, sys.version_info[:3])), "upstream": revision,
                      "fixtures": len(fixtures), "result_bits": result_bits, "float_result_bits": float_bits,
                      "subtraction_bits": sub_bits, "multiplication_bits": mul_bits, "division_bits": div_bits,
                      "observations": observed,
                      "nonfinite_result": {"cpython_bits": "7ff0000000000000", "lean": "unsupported"},
                      "float_overflow": {"cpython_bits": ["7ff0000000000000", "fff0000000000000"],
                                         "lean": "unsupported"},
                      "subtraction_overflow": {"cpython_bits": ["7ff0000000000000", "fff0000000000000"],
                                               "lean": "unsupported"},
                      "multiplication_overflow": {"cpython_bits": ["7ff0000000000000", "fff0000000000000"],
                                                  "lean": "unsupported"},
                      "division_overflow": {"cpython_bits": ["7ff0000000000000", "fff0000000000000"],
                                            "lean": "unsupported"}}))
