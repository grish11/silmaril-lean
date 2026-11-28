# SPDX-License-Identifier: MIT
"""Replay closed integer power and the test_pow.py cutoff against CPython 3.13.5."""

import argparse
import ast
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile

NUMERIC = runpy.run_path(str(Path(__file__).with_name("check-python-numeric-arguments.py")))
PIN = "tests/python/programs/original/lambda-py/python-reference/types/test_pow.py"
SHA256 = "d4847f86391fd6f798398e33c55e18e1aba74ac078c350cda8cc80bb74395478"
HELPER = "___assertEqual"
STOCK = '(initial "legacy_builtin")'


def assert_equal(left, right):
    assert left == right, (left, right)


def replay(checkout, paths):
    suite = NUMERIC["SUITE"]
    source = suite["pinned_source"](checkout, PIN, SHA256)
    last = ast.parse(source).body[-1]
    prefix = "".join(source.splitlines(keepends=True)[:last.lineno - 1])
    suffix = "".join(source.splitlines(keepends=True)[last.lineno - 1:])
    check, cpython = NUMERIC["check"], NUMERIC["cpython"]
    literal_guard, seeded, receipts = (NUMERIC[name] for name in ("literal_guard", "seeded", "receipts"))
    missing = f"NameError:{HELPER}"
    values = [(0, 0), (1, 1), (1, 1), (17, 17), (1024, 1024)]
    float_pair = (0.25, 0.25)

    assert cpython(source, {}) == (missing, {})
    assert cpython(prefix, {}) == (missing, {})
    guards = [
        literal_guard(HELPER, values),
        f'#guard ordinaryArguments pythonSource "{missing}" []',
        seeded("Namespace.empty", missing, "[]",
               receipts(HELPER, f'.error (.raised (.runtime (.nameError "{HELPER}")))')),
    ]
    for placement in ("builtin", "preamble"):
        trace = []

        def observe(left, right):
            trace.append((left, right))
            assert_equal(left, right)

        builtins = {HELPER: observe} if placement == "builtin" else {}
        initial = {HELPER: observe} if placement == "preamble" else {}
        assert cpython(prefix, builtins, initial) == ("normal", initial)
        assert trace == values and all(type(value) is int for pair in trace for value in pair)
        trace.clear()
        assert cpython(source, builtins, initial) == ("normal", initial)
        assert trace == values + [float_pair]
        assert all(type(value) is float for value in trace[-1])
        space = f'(initial "legacy_{placement}")'
        guards.append(seeded(space, "normal", f"{space}.moduleGlobals", receipts(HELPER, ".ok .none", len(values))))

    check(prefix, paths, *guards)
    check(source, paths, NUMERIC["REJECTED"])
    check(suffix, paths, NUMERIC["REJECTED"])
    return {"sha256": SHA256, "integer_pairs": values, "stock_prefix_receipts": len(values),
            "empty_and_ordinary_prefix": missing,
            "first_remaining_statement": last.lineno, "cpython_final_float": float_pair[0]}


def controls(paths):
    check, cpython = NUMERIC["check"], NUMERIC["cpython"]
    literal_guard, seeded, receipts = (NUMERIC[name] for name in ("literal_guard", "seeded", "receipts"))
    stock = {HELPER: assert_equal}
    expressions = ("(-3)**5", "(-3)**6", "-2**2", "2**3**2", "2**~(-3)",
                   "2**2048", "0**4096", "0**0")
    values = [eval(compile(expr, "<integer power>", "eval", optimize=0), {"__builtins__": {}})
              for expr in expressions]
    assert all(type(value) is int for value in values)
    source = "".join(f"{HELPER}({expr}, {value})\n" for expr, value in zip(expressions, values, strict=True))
    assert cpython(source, stock) == ("normal", {})
    check(source, paths, literal_guard(HELPER, [(value, value) for value in values]),
          seeded(STOCK, "normal", "[]", receipts(HELPER, ".ok .none", len(values))))

    source = f"keep = 7\n{HELPER} = None\n{HELPER}(2**3, missing_right)\ntail = 9\n"
    status = "NameError:missing_right"
    assert cpython(source, stock) == (status, {"keep": 7, HELPER: None})
    check(source, paths, seeded(STOCK, status, f'[("{HELPER}", .none), ("keep", .int 7)]',
                                receipts(HELPER, '.error (.raised (.runtime (.nameError "missing_right")))')),
          f'#guard ordinaryArguments pythonSource "{status}" '
          f'[("{HELPER}", some .none), ("keep", some (.int 7)), ("tail", none)]')

    source = "keep = 7\nif (-2)**3 != -8: raise Exception('power')\ntail = 9\n"
    assert cpython(source, {}) == ("normal", {"keep": 7, "tail": 9})
    check(source, paths, seeded("Namespace.empty", "normal", '[("tail", .int 9), ("keep", .int 7)]', "[]"),
          '#guard ordinaryArguments pythonSource "normal" [("keep", some (.int 7)), ("tail", some (.int 9))]')

    for expr in ("2**2049", "0**4097", "2**-2", "2.0**2", "5 / 2"):
        source = f"{HELPER}({expr}, {expr})\n"
        assert cpython(source, stock) == ("normal", {})
        check(source, paths, NUMERIC["REJECTED"])
    for expr, expected in (("0**-1", ZeroDivisionError), ("(1 << 2000)**-1", OverflowError),
                           ("5 / 0", ZeroDivisionError)):
        source = f"keep = 7\n{HELPER}({expr}, missing_right)\ntail = 9\n"
        namespace = {"__builtins__": stock}
        try:
            exec(compile(source, "<numeric error order>", "exec", optimize=0), namespace)
        except expected as error:
            assert type(error) is expected and namespace == {"__builtins__": stock, "keep": 7}
        else:
            raise AssertionError(f"CPython completed {expr}")
        check(source, paths, NUMERIC["REJECTED"])


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path, required=True)
    args = parser.parse_args()
    assert sys.version_info[:3] == (3, 13, 5), sys.version
    revision = subprocess.check_output(["git", "-C", str(args.upstream), "rev-parse", "HEAD"], text=True).strip()
    assert revision == NUMERIC["SUITE"]["UPSTREAM_REVISION"], revision
    with tempfile.TemporaryDirectory() as directory:
        source = Path(directory) / "Fixture.py"
        paths = source, source.with_suffix(".lean")
        pin = replay(args.upstream, paths)
        controls(paths)
    print(json.dumps({"cpython": "3.13.5", "upstream": revision, "test_pow.py": pin, "controls": "passed"}))
