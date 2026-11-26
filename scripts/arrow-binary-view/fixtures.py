#!/usr/bin/env python3
"""Check the frozen PyArrow BinaryView/Utf8View buffers.

With --regenerate, reproduce each buffer in memory using the pinned wheel.
"""

import argparse
import hashlib
import re
from pathlib import Path
import sys


FIXTURE_SOURCE = Path(__file__).resolve().parents[2] / "Silmaril/Formats/Arrow/BinaryView/Fixture.lean"
PYARROW_VERSION = "26.0.1"
VALUES = [
    ["", "α", "abcdefghijkl", "abcdefghijklm", "🧪" * 4],
    ["abcdefghijklm", "xyz" * 6, None],
]
FIXTURES = ("validity", "slots", "firstData", "secondData")
SHA256S = (
    "620bfdaa346b088fb49998d92f19a7eaf6bfc2fb0aee015753966da1028cb731",
    "4075c779196967949ea7f681b255238ab7169d6601475cbc6f4467c2c023033e",
    "3a0e67851f0f2e3c3df79af2563029aff326fc07de9ef7a05cc6d9a817c6ef73",
    "932fbd45f3e9933a0c893a3491d8a68ec8d1e932a6390430aac7cd9397b49dbc",
)


def produce():
    import pyarrow as pa

    if sys.byteorder != "little" or pa.__version__ != PYARROW_VERSION:
        raise SystemExit(f"fixture requires little-endian PyArrow {PYARROW_VERSION}")
    strings = pa.concat_arrays([pa.array(values, type=pa.string_view()) for values in VALUES])
    binaries = pa.concat_arrays([
        pa.array([value.encode() if value is not None else None for value in values],
                 type=pa.binary_view())
        for values in VALUES
    ])
    expected = sum(VALUES, [])
    if strings.to_pylist() != expected:
        raise SystemExit("unexpected Utf8View values")
    if binaries.to_pylist() != [value.encode() if value is not None else None for value in expected]:
        raise SystemExit("unexpected BinaryView values")
    string_buffers = [buffer.to_pybytes() for buffer in strings.buffers()]
    if string_buffers != [buffer.to_pybytes() for buffer in binaries.buffers()]:
        raise SystemExit("BinaryView and Utf8View physical buffers differ")
    if string_buffers[0] != b"\x7f" or len(string_buffers) != len(FIXTURES):
        raise SystemExit("unexpected validity or number of variadic buffers")
    return string_buffers


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--regenerate", action="store_true")
    args = parser.parse_args()
    regenerated = produce() if args.regenerate else None
    source = FIXTURE_SOURCE.read_text(encoding="utf-8")
    for index, (name, expected_hash) in enumerate(zip(FIXTURES, SHA256S, strict=True)):
        match = re.search(rf"^def {name} : KBytes :=\n  \.leaf (\d+) 0x([0-9a-f]+)$",
                          source, re.MULTILINE)
        if match is None:
            raise SystemExit(f"fixture definition missing for {name}")
        length, packed = match.groups()
        fixture = int(packed, 16).to_bytes(int(length), "little")
        digest = hashlib.sha256(fixture).hexdigest()
        if digest != expected_hash or (regenerated is not None and fixture != regenerated[index]):
            raise SystemExit(f"unexpected fixture bytes in {name}: {digest}")
        print(f"{name} ({len(fixture)} bytes) SHA-256 {digest}")


if __name__ == "__main__":
    main()
