#!/usr/bin/env python3
"""Compare last-hit/miss lookup; materialize both indexes before timing either engine."""

import argparse
import statistics
import subprocess
import tempfile
import time
from pathlib import Path


def trie(entries, bit=0):
    if not entries:
        return ".empty"
    if bit == 32:
        [(_, value)] = entries
        return f"(.node (some {value}) .empty .empty)"
    mask = 1 << (31 - bit)
    zero = [entry for entry in entries if not entry[0] & mask]
    one = [entry for entry in entries if entry[0] & mask]
    return f"(.node none {trie(zero, bit + 1)} {trie(one, bit + 1)})"


def fixture(count):
    entries = [(0x01550000 + index, index + 1) for index in range(count)]
    rows = [f"({list(key.to_bytes(4, 'big'))}, {value})" for key, value in entries]
    chunks = [rows[start:start + 64] for start in range(0, count, 64)]
    declarations = []
    for index in reversed(range(len(chunks))):
        tail = "[]" if index + 1 == len(chunks) else f"chunk{index + 1}"
        items = " :: ".join(chunks[index])
        declarations.append(f"def chunk{index} : List (List UInt8 × Nat) := {items} :: {tail}")
    chunk_defs = "\n".join(declarations)
    return f"""module
public import Silmaril.Semantics.Naming.Table.Defs
set_option maxRecDepth 8192
@[expose] public section
open Silmaril.Semantics.Naming
def radixIndex : Table Nat := {trie(entries)}
{chunk_defs}
def linearIndex : List (List UInt8 × Nat) := chunk0
def key (index : Nat) : List UInt8 := [1, 0x55, UInt8.ofNat (index / 256), UInt8.ofNat index]
def radix (index : Nat) : Option Nat := radixIndex.lookup (Table.byteRoute (key index))
def linear (index : Nat) : Option Nat :=
  linearIndex.findSome? fun (name, value) => if name == key index then some value else none
"""


def run(directory, *args):
    start = time.perf_counter()
    result = subprocess.run(["lean", *args], cwd=directory, check=True, capture_output=True, text=True, timeout=120)
    return result.stdout.strip(), (time.perf_counter() - start) * 1000


def benchmark(directory, count, queries, iterations):
    (directory / "NamingBenchFixture.lean").write_text(fixture(count), encoding="utf-8")
    _, build = run(directory, "-o", "NamingBenchFixture.olean", "NamingBenchFixture.lean")
    head = "module\nimport NamingBenchFixture\nset_option maxRecDepth 8192\nset_option maxHeartbeats 0\n"
    baseline = []
    (directory / "Baseline.lean").write_text(head, encoding="utf-8")
    for _ in range(3):
        baseline.append(run(directory, "Baseline.lean")[1])
    print(f"rows={count} import-only={statistics.median(baseline):.1f}ms fixture-build={build:.1f}ms")
    for lookup in ("radix", "linear"):
        kernel = head + "".join(f"#reduce {lookup} {index}\n" for index in range(count - queries, count + queries))
        (directory / "Kernel.lean").write_text(kernel, encoding="utf-8")
        readings = []
        expected = [f"some {index}" for index in range(count - queries + 1, count + 1)] + ["none"] * queries
        for _ in range(3):
            result, elapsed = run(directory, "Kernel.lean")
            if result.splitlines() != expected:
                raise ValueError(f"unexpected kernel answers for {lookup}: {result}")
            readings.append(elapsed)
        compiled = head.replace("import NamingBenchFixture", "import NamingBenchFixture\nmeta import NamingBenchFixture") + f"""
public def main (args : List String) : IO Unit := do
  let some iterations := args.head?.bind String.toNat? | throw (IO.userError "expected count")
  let start ← IO.monoNanosNow
  let mut checksum := 0
  for index in [:iterations] do
    checksum := checksum + ({lookup} ({count - queries} + index % {queries * 2})).getD 0
  let stop ← IO.monoNanosNow
  IO.println s!"{{checksum}} {{stop - start}}"
"""
        (directory / "Compiled.lean").write_text(compiled, encoding="utf-8")
        vm_readings = []
        checksum = sum(range(count - queries + 1, count + 1)) * (iterations // (queries * 2))
        for _ in range(3):
            result, _ = run(directory, "--run", "Compiled.lean", str(iterations))
            total, nanoseconds = map(int, result.split())
            if total != checksum:
                raise ValueError(f"unexpected compiled checksum for {lookup}: {total}")
            vm_readings.append(nanoseconds / 1_000_000)
        print(f"  {lookup:6s} kernel {2 * queries} probes, wall={statistics.median(readings):.1f}ms; "
              f"compiled VM {iterations} probes, loop={statistics.median(vm_readings):.1f}ms")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("rows", nargs="*", type=int, default=[64, 256, 1024])
    parser.add_argument("--queries", type=int, default=16, help="number of hit and miss keys each")
    parser.add_argument("--iterations", type=int, default=8192, help="iteration count in the compiled loop")
    args = parser.parse_args()
    if args.queries < 1 or not all(args.queries <= count <= 4096 for count in args.rows):
        parser.error("require 1 <= queries <= rows <= 4096")
    if args.iterations < 1 or args.iterations % (2 * args.queries):
        parser.error("iterations must be a positive multiple of twice queries")
    with tempfile.TemporaryDirectory() as temporary:
        directory = Path(temporary)
        try:
            for count in args.rows:
                benchmark(directory, count, args.queries, args.iterations)
        except subprocess.CalledProcessError as error:
            parser.exit(error.returncode, error.stdout + error.stderr)


if __name__ == "__main__":
    main()
