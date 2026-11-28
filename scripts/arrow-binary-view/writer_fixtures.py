#!/usr/bin/env python3
"""Reproduce pinned view column fixtures and read Lean-emitted buffers."""

import argparse
import hashlib
import os
from pathlib import Path
import struct
import subprocess
import sys

import pyarrow as pa


ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "Silmaril/Formats/Arrow/BinaryView/Column/Writer/Fixture.lean"
DRIVER = ROOT / "scripts/arrow-binary-view/ColumnWriter.lean"


def expected_cases():
    for name, kind, mixed, prefix, suffix in (
        ("binary", pa.binary_view(), [None, b"", b"\xff" * 12, bytes(13), b"tail" * 6],
         b"ignored binary prefix", b"ignored binary suffix"),
        ("utf8", pa.string_view(), [None, "", "é" * 6, "é" * 6 + "x", "雪" * 9],
         "ignored UTF-8 prefix 雪", "ignored UTF-8 suffix 雪"),
    ):
        yield (name, "Mixed", kind, mixed, pa.array([prefix, *mixed, suffix], type=kind).slice(1, len(mixed)))
        yield (name, "Inline", kind, mixed[1:3], pa.array(mixed[1:3], type=kind))
        yield (name, "Nulls", kind, [None, None], pa.nulls(2, type=kind))
        yield (name, "Empty", kind, [], pa.array([], type=kind))


def physical_windows(array):
    validity, views, *data = array.buffers()
    rows = len(array)
    offset = array.offset
    # Shift the bitmap to logical row zero and retain the original
    # variadic buffers, whose offsets are still referenced by the views.
    if validity is None:
        bitmap = b""
    else:
        bits = int.from_bytes(validity, "little") >> offset
        bitmap = (bits & ((1 << rows) - 1)).to_bytes((rows + 7) // 8, "little")
    return bitmap, views.slice(16 * offset, 16 * rows).to_pybytes(), [part.to_pybytes() for part in data]


def leaf(data):
    return f".leaf {len(data)} 0x{int.from_bytes(data, 'little'):x}"


def produce():
    lines = [
        "module\n\npublic import Silmaril.Formats.Arrow.BinaryView.Column.Defs\n\n",
        "/-! Produced by scripts/arrow-binary-view/writer_fixtures.py. -/\n\n",
        "@[expose] public section\n\n",
        "namespace Silmaril.Formats.Arrow.BinaryView.Column.Writer.Fixture\n\n",
    ]
    for prefix, name, _, values, array in expected_cases():
        array.validate(full=True)
        assert array.to_pylist() == values
        validity, views, data = physical_windows(array)
        buffers = ", ".join(leaf(part) for part in data)
        label = prefix + name
        print(f"PyArrow {label}: offset={array.offset}, rows={len(array)}, nulls={array.null_count}, "
              f"data buffers={len(data)}, SHA-256={hashlib.sha256(validity + views + b''.join(data)).hexdigest()}")
        lines.append(f"def {label} : FieldNode × Buffers :=\n"
                     f"  ⟨⟨{len(array)}, {array.null_count}⟩, ⟨{leaf(validity)},\n"
                     f"    ⟨{leaf(views)}, #[{buffers}]⟩⟩⟩\n\n")
    lines.append("end Silmaril.Formats.Arrow.BinaryView.Column.Writer.Fixture\n")
    return "".join(lines)


def read_emitted(directory):
    subprocess.run([
        os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
        "-DwarningAsError=true", "--run", str(DRIVER), str(directory),
    ], cwd=ROOT, check=True)
    for prefix, name, kind, values, _ in expected_cases():
        stem = directory / (prefix + name)
        rows, nulls, count = map(int, (stem / "node.txt").read_text().split())
        validity = (stem / "validity.bin").read_bytes()
        views = (stem / "views.bin").read_bytes()
        raw_values = [v.encode() if prefix == "utf8" and v is not None else v for v in values]
        joined = b"".join(v for v in raw_values if v is not None and len(v) > 12)
        data = [(stem / f"data-{i}.bin").read_bytes() for i in range(count)]
        assert (rows, nulls, count) == (len(values), values.count(None), int(bool(joined)))
        assert len(views) == 16 * rows and len(validity) == (rows + 7) // 8
        assert data == ([joined] if joined else [])
        offset = 0
        for row, value in enumerate(raw_values):
            encoding = views[16 * row:16 * (row + 1)]
            assert bool(validity[row // 8] & (1 << (row % 8))) == (value is not None)
            if value is None:
                assert encoding == bytes(16)
            elif len(value) <= 12:
                assert encoding == struct.pack("<i12s", len(value), value)
            else:
                assert encoding == struct.pack("<i4sii", len(value), value[:4], 0, offset)
                offset += len(value)
        observed = pa.Array.from_buffers(kind, rows, [
            pa.py_buffer(validity) if validity else None,
            pa.py_buffer(views), *(pa.py_buffer(part) for part in data),
        ], null_count=nulls)
        observed.validate(full=True)
        assert observed.to_pylist() == values and observed.null_count == nulls
        print(f"Lean {stem.name} read by PyArrow: rows={rows}, nulls={nulls}, data buffers={count}, "
              f"SHA-256={hashlib.sha256(validity + views + b''.join(data)).hexdigest()}")


def main():
    if sys.byteorder != "little" or pa.__version__ != pa.cpp_build_info.version or pa.__version__ != "26.0.1":
        raise SystemExit("requires little-endian PyArrow 26.0.1")
    parser = argparse.ArgumentParser(description=__doc__)
    options = parser.add_mutually_exclusive_group(required=True)
    options.add_argument("--write", type=Path, help="write the reproduced PyArrow fixture module")
    options.add_argument("--out", type=Path, help="write and validate emitted Lean buffers in this directory")
    args = parser.parse_args()
    fixtures = produce()
    if args.write:
        args.write.write_text(fixtures, encoding="utf-8")
    else:
        if FIXTURE.read_text(encoding="utf-8") != fixtures:
            raise SystemExit("pinned PyArrow buffers differ from the checked Lean fixture")
        read_emitted(args.out.resolve())


if __name__ == "__main__":
    main()
