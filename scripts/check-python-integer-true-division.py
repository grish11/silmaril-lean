# SPDX-License-Identifier: MIT
"""Compare Python's checked integer quotient with CPython 3.13.5."""

import argparse
import ast
import hashlib
import json
import os
from pathlib import Path
import runpy
import struct
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
UPSTREAM = "b7ff99372dd24845cf84e58c96b877f15764b276"
PIN = "tests/python/programs/original/lambda-py/python-reference/types/test_int_float_primitives.py"
SHA256 = "6c8ae62ff190d091181229ae2ef72ccd3959f29b025353ecf4b89f0cba1903d4"

LEAN = """module
import Silmaril.Languages.Python.Core.Binary64.Thms
import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Thms
meta import Silmaril.Languages.Python.Core.Binary64.Defs
meta import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Defs

open Silmaril.Languages.Python
open Source
open Core.Binary64

private def observedBits (numerator divisor : Int) : Except DivisionError UInt64 :=
  (trueDivide numerator divisor).map fun value => value.val.bits
"""


def bits(value):
    assert type(value) is float
    return struct.pack(">d", value).hex()


def cpython(numerator, divisor):
    try:
        return "float", bits(numerator / divisor)
    except (ZeroDivisionError, OverflowError) as error:
        return type(error).__name__, None


def pinned_operand(checkout):
    revision = subprocess.check_output(["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()
    assert revision == UPSTREAM, revision
    source = (checkout / PIN).read_bytes()
    assert hashlib.sha256(source).hexdigest() == SHA256
    module = ast.parse(source)
    statement = next(node for node in module.body if node.lineno == 28)
    expression = statement.value.args[0]
    assert isinstance(expression, ast.BinOp) and isinstance(expression.op, ast.Div)
    original_call = ast.Module(body=[statement], type_ignores=[])
    observed = []

    def compare(left, right):
        observed.append((bits(left), bits(right)))

    exec(compile(original_call, PIN, "exec", optimize=0), {"__builtins__": {"___assertEqual": compare}})
    assert observed == [("4004000000000000", "4004000000000000")]

    emit = runpy.run_path(str(ROOT / "tools/python-source/source_ast.py"))["emit"]
    declarations = []
    first_call = ast.Module(body=module.body[:1], type_ignores=[])
    for name, tree in (("original", module), ("firstCall", first_call), ("divisionCall", original_call)):
        term = emit(tree, source.decode("utf-8")).split("public def pythonSource : Module :=", 1)[1]
        declarations.append(f"private def {name} : Module :={term}")
    declarations.append("""
#guard (match Compile.ModuleEntry.Functions.Run.compile original with
  | .error (.source (.scalar .expressionProfile)) => true
  | _ => false)
#guard (Compile.ModuleEntry.Functions.Run.compile firstCall).isOk
#guard (Compile.ModuleEntry.Functions.Run.compile divisionCall).isOk
""")
    return (expression.left.value, expression.right.value), "\n".join(declarations)


def controls(pinned):
    midpoint = 2**1024 - 2**970
    return (
        ("pinned quotient", *pinned, ("float", "4004000000000000")),
        ("positive tenth", 1, 10, ("float", "3fb999999999999a")),
        ("negative numerator", -5, 2, ("float", "c004000000000000")),
        ("negative divisor", 5, -2, ("float", "c004000000000000")),
        ("both negative", -5, -2, ("float", "4004000000000000")),
        ("positive zero", 0, 3, ("float", "0000000000000000")),
        ("negative zero", 0, -3, ("float", "8000000000000000")),
        ("lower even normal tie", 2**53 + 1, 2**53, ("float", "3ff0000000000000")),
        ("upper even normal tie", 2**53 + 3, 2**53, ("float", "3ff0000000000002")),
        ("separate operand rounding counterexample", 2**53 - 5, 2**53 + 1, ("float", "3feffffffffffffa")),
        ("huge operands with finite quotient", 2**4096, 2**4097, ("float", "3fe0000000000000")),
        ("smallest subnormal", 1, 2**1074, ("float", "0000000000000001")),
        ("underflow tie to negative zero", -1, 2**1075, ("float", "8000000000000000")),
        ("underflow tie to positive zero", 1, 2**1075, ("float", "0000000000000000")),
        ("upper even subnormal tie", 3, 2**1075, ("float", "0000000000000002")),
        ("tie between subnormal and normal", 2**53 - 1, 2**1075, ("float", "0010000000000000")),
        ("below overflow midpoint", 3 * midpoint - 1, 3, ("float", "7fefffffffffffff")),
        ("overflow midpoint", midpoint, 1, ("OverflowError", None)),
        ("above overflow midpoint", 3 * midpoint + 1, 3, ("OverflowError", None)),
        ("negative overflow", midpoint, -1, ("OverflowError", None)),
        ("zero divisor", 5, 0, ("ZeroDivisionError", None)),
        ("zero over zero", 0, 0, ("ZeroDivisionError", None)),
    )


def check(checkout):
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5), sys.version
    info = sys.float_info
    assert (info.radix, info.mant_dig, info.min_exp, info.max_exp, info.rounds) == (2, 53, -1021, 1024, 1)
    pinned, declarations = pinned_operand(checkout)
    rounded_operands = bits(float(2**53 - 5) / float(2**53 + 1))
    assert rounded_operands == "3feffffffffffffb"

    observations = {}
    guards = []
    for label, numerator, divisor, expected in controls(pinned):
        observed = cpython(numerator, divisor)
        assert observed == expected, (label, observed, expected)
        kind, payload = observed
        if kind == "float":
            lean = f".ok 0x{payload}"
        else:
            lean = ".error .zeroDivisionError" if kind == "ZeroDivisionError" else ".error .overflowError"
        guards.append(f"#guard observedBits ({numerator}) ({divisor}) == {lean}")
        observations[label] = f"0x{payload}" if payload is not None else kind
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "IntegerTrueDivision.lean"
        path.write_text(LEAN + "\n" + declarations + "\n" + "\n".join(guards) + "\n", encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(path)], cwd=ROOT, check=True, timeout=90)
    return {"cpython": "3.13.5", "upstream": UPSTREAM, "pin": {"sha256": SHA256, "line": 28},
            "controls": observations, "round_operands_first": f"0x{rounded_operands}"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(check(args.upstream)))
