#!/usr/bin/env python3
"""Check positional projection of the pinned PyArrow carrier-window file."""
import argparse
import hashlib
import struct
from pathlib import Path

import pyarrow as pa


CARRIER_SHA256 = "f1c55f598ee91bf522d50e582121f977ed4c62cda5be64026b95dcda0215e9ee"
WINDOW_STOP = 1354


def check(path):
    if pa.__version__ != "26.0.1":
        raise SystemExit("fixture requires PyArrow 26.0.1")
    source = path.read_bytes()
    assert hashlib.sha256(source).hexdigest() == CARRIER_SHA256

    with pa.ipc.open_file(source, footer_offset=WINDOW_STOP) as reader:
        first = reader.get_batch(0)
        first.validate(full=True)
        selected = first.select([1, 0, 1])
        expected_fields = [pa.field("octets", pa.binary_view()), pa.field("signed", pa.int32())]
        assert selected.schema.equals(pa.schema([expected_fields[i] for i in [0, 1, 0]]),
                                      check_metadata=True)
        assert [column.to_pylist() for column in selected.columns] == [
            [b"", None, b"\xff" * 12, bytes(range(13))],
            [-7, None, 42, -2147483648],
            [b"", None, b"\xff" * 12, bytes(range(13))],
        ]
        assert selected.num_rows == 4
        empty = reader.get_batch(1)
        empty.validate(full=True)
        assert [(batch.select([]).num_rows, batch.select([]).num_columns)
                for batch in [first, empty]] == [(4, 0), (0, 0)]
        assert reader.num_record_batches == 3
        print("exact repeated/reordered fields and slots; zero-width row counts 4 and 0")

    for bad, good, rows, offset, replacement, needle in [
        (0, 2, 2, 572, b"\xff", "inlined prefix"),
        (2, 0, 4, 1040, struct.pack("<I", 2**31), "negative size"),
    ]:
        corrupted = source[:offset] + replacement + source[offset + len(replacement):]
        with pa.ipc.open_file(corrupted, footer_offset=WINDOW_STOP) as reader:
            for index, expected_rows in [(good, rows), (1, 0)]:
                batch = reader.get_batch(index)
                batch.validate(full=True)
                assert batch.select([0]).num_rows == expected_rows
            try:
                reader.get_batch(bad).validate(full=True)
            except pa.ArrowInvalid as error:
                assert needle in str(error)
            else:
                raise AssertionError("expected the selected batch to fail before projection")
        print(f"selected batch {bad} rejected before projection; neighbors {good} and 1 read")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("carrier", type=Path)
    check(parser.parse_args().carrier)
