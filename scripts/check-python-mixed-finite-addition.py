# SPDX-License-Identifier: MIT
"""Replay finite mixed-addition call operands against CPython."""

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


def nonfinite_control():
    source = PREFIX + f"bad = relay({MAX_FINITE_INTEGER} + 1.7976931348623157e308)\ntail = 9\n"
    status, _, namespace, _ = EQUALITY["cpython"](source, "ordinary")
    assert status == "normal"
    assert bits(namespace.pop("bad")) == "7ff0000000000000"
    assert namespace.pop("tail") == 9
    values, functions = TRANSPORT["state"](namespace)
    guards = [TRANSPORT["ordinary"](".executorFault .unsupportedFloatOperand", values, functions, '["bad", "tail"]')]
    prior = TRANSPORT["success_receipt"]("relay", namespace["result"])
    guards.extend(TRANSPORT["seeded"](space, ".error .unsupported", values, functions, f"[{prior}]")
                  for _, space in EQUALITY["PROFILES"])
    return (source, "\n".join(guards))


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

    fixtures.append(nonfinite_control())
    rejected = """#guard (match compile pythonSource with
  | .error (.source (.scalar .expressionProfile)) => true
  | _ => false)"""
    fixtures.extend((f"relay({expression})\n", rejected) for expression in
                    ("4.0 + 2.0", "(4 + 2.0) + 1", "4 + 1e999"))
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
    fixtures, observed, result_bits = controls(args.upstream)
    with tempfile.TemporaryDirectory() as directory:
        source, lean = Path(directory) / "Fixture.py", Path(directory) / "Fixtures.lean"
        INTAKE["check_lean_batch"](source, lean, fixtures, EQUALITY["LEAN"], extra_imports=TRANSPORT["SUITE"]["IMPORTS"])
    print(json.dumps({"cpython": ".".join(map(str, sys.version_info[:3])), "upstream": revision,
                      "fixtures": len(fixtures), "result_bits": result_bits, "observations": observed,
                      "nonfinite_result": {"cpython_bits": "7ff0000000000000", "lean": "unsupported"}}))
