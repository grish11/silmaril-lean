"""Check exact DATE narrowing against pinned PyArrow IPC streams."""

import argparse
from datetime import date
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
TESTS = ROOT / "Silmaril/Formats/Arrow/DateStream/Narrow/Tests.lean"
MIN = -(2**31)
MAX = 2**31 - 1
MS_PER_DAY = 86_400_000
LEAP_DAY = (date(2000, 2, 29) - date(1970, 1, 1)).days
FIELD = "日付"


def milliseconds(batches):
    return [[None if day is None else day * MS_PER_DAY for day in batch] for batch in batches]


def ipc_stream(pa, kind, storage, raw_batches):
    schema = pa.schema([pa.field(FIELD, kind, nullable=True)])
    sink = pa.BufferOutputStream()
    with pa.ipc.new_stream(sink, schema) as writer:
        for raw_slots in raw_batches:
            cells = pa.array(raw_slots, type=storage).view(kind)
            writer.write_batch(pa.RecordBatch.from_arrays([cells], schema=schema))
    wire = sink.getvalue().to_pybytes()
    with pa.ipc.open_stream(wire) as reader:
        assert reader.schema == schema
        reread = [batch.column(0).view(storage).to_pylist() for batch in reader]
        assert reread == raw_batches
    return wire


def wire_term(wire):
    return f"(KBytes.leaf {len(wire)} 0x{int.from_bytes(wire, 'little'):x})"


def slots_term(batches):
    return "[" + ", ".join(
        "[" + ", ".join("none" if day is None else f"some ({day})" for day in batch) + "]"
        for batch in batches
    ) + "]"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pyarrow-path", type=Path, help="Directory containing unpacked PyArrow")
    args = parser.parse_args()
    if args.pyarrow_path:
        sys.path.insert(0, str(args.pyarrow_path.resolve()))
    import pyarrow as pa
    import pyarrow.compute as pc

    pin = json.loads((HERE / "fixtures.json").read_text())
    assert platform.python_implementation() == "CPython"
    assert platform.python_version() == pin["cpython"]
    assert pa.__version__ == pin["pyarrow"]

    admitted = [[MIN, -1, None], [], [0, LEAP_DAY, MAX]]
    for expected, scaled in zip(admitted, milliseconds(admitted), strict=True):
        narrow = pa.array(expected, type=pa.int32()).view(pa.date32())
        assert pc.cast(narrow, pa.date64()).view(pa.int64()).to_pylist() == scaled

    cases = {
        "admitted": (64, milliseconds(admitted), f"observes {{wire}} {slots_term(admitted)}"),
        "underflow": (64, milliseconds([[-1], [None, MIN - 1]]),
                      f"rejects {{wire}} (.outOfRange 1 1 ({MIN - 1}))"),
        "overflow": (64, milliseconds([[-1], [None, MAX + 1]]),
                     f"rejects {{wire}} (.outOfRange 1 1 {MAX + 1})"),
        # Date64 can transport these raw words, but the DATE reader must reject the remainder.
        "nonwhole": (64, [[0], [None, -1]],
                     "rejects {wire} (.reader (.batch 1 (.values (.nonWholeDay 1))))"),
        # An earlier range error is possible only after the whole stream has been admitted.
        "precedence": (64, [[(MAX + 1) * MS_PER_DAY], [None, -1]],
                       "rejects {wire} (.reader (.batch 1 (.values (.nonWholeDay 1))))"),
        "wrong_unit": (32, [[-1, None]], "rejects {wire} (.wrongUnit .day)"),
    }
    fixtures = {}
    guards = []
    for name, (bits, batches, guard) in cases.items():
        if bits == 64:
            wire = ipc_stream(pa, pa.date64(), pa.int64(), batches)
        else:
            wire = ipc_stream(pa, pa.date32(), pa.int32(), batches)
        fixtures[name] = {"bytes": len(wire), "sha256": hashlib.sha256(wire).hexdigest(),
                          "word_bits": bits, "raw_batches": batches}
        guards.append("#guard " + guard.format(wire=wire_term(wire)))

    assert fixtures == pin["fixtures"], json.dumps(fixtures, indent=2)
    with tempfile.TemporaryDirectory(prefix="date64-narrow-") as directory:
        harness = Path(directory) / "Oracle.lean"
        harness.write_text(TESTS.read_text(encoding="utf-8") + "\n" + "\n".join(guards) + "\n",
                           encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(harness)], cwd=ROOT, check=True)
    print(f"PASS {len(fixtures)} pinned IPC streams, including exact Date32 endpoints and error precedence")


if __name__ == "__main__":
    main()
