"""Check Lean-written Arrow IPC bodies or streams with the pinned PyArrow reader."""
import argparse
import hashlib
import json
from pathlib import Path

import numpy as np
import pyarrow as pa

HERE = Path(__file__).resolve().parent
PRODUCER = json.loads((HERE / "fixture.json").read_text(encoding="utf-8"))["producer"]
TYPES = {"int32": (pa.int32(), 2), "utf8": (pa.string(), 3)}
CASES = {
    "mixed": (
        [("n", True, "int32"), ("téxt", True, "utf8")],
        [(-2147483648, "é"), (None, ""), (2147483647, None), (-1, "雪"),
         (0, "🧪"), (None, None), (42, "a"), (17, ""), (8, "λ")],
    ),
    "empty": ([("n", False, "int32"), ("téxt", True, "utf8")], []),
    "zero-columns": ([], [(), (), ()]),
}


def check(directory, name, schema, expected):
    meta = json.loads((directory / f"{name}.json").read_text(encoding="utf-8"))
    body = (directory / f"{name}.body").read_bytes()
    row_count = meta["rowCount"]
    assert row_count == len(expected)
    assert len(body) % 8 == 0
    assert [(f["name"], f["nullable"], f["type"]) for f in meta["fields"]] == schema
    assert len(meta["nodes"]) == len(schema)
    assert len(meta["buffers"]) == sum(TYPES[kind][1] for _, _, kind in schema)
    ranges = iter(meta["buffers"])
    arrays = []
    fields = []
    previous_end = 0
    for (field, nullable, kind), node in zip(schema, meta["nodes"], strict=True):
        arrow_type, buffer_count = TYPES[kind]
        fields.append(pa.field(field, arrow_type, nullable=nullable))
        assert node["length"] == row_count
        buffers = []
        for index in range(buffer_count):
            descriptor = next(ranges)
            start, size = descriptor["offset"], descriptor["length"]
            assert size >= 0
            assert start % 8 == 0 and previous_end <= start <= len(body) - size
            assert not any(body[previous_end:start])
            buffers.append(None if index == 0 and size == 0
                           else pa.py_buffer(memoryview(body)[start:start + size]))
            previous_end = start + size
        array = pa.Array.from_buffers(arrow_type, row_count, buffers, null_count=-1)
        assert array.null_count == node["nullCount"]
        assert nullable or array.null_count == 0
        array.validate(full=True)
        arrays.append(array)
    assert not any(body[previous_end:])
    if arrays:
        batch = pa.RecordBatch.from_arrays(arrays, schema=pa.schema(fields))
    else:
        assert not body
        batch = pa.RecordBatch.from_struct_array(pa.array([{}] * row_count, type=pa.struct([])))
    assert batch.num_rows == row_count
    batch.validate(full=True)
    assert [tuple(row.values()) for row in batch.to_pylist()] == expected
    print(f"{name}: {row_count} rows, {len(body)} body bytes, SHA-256 {hashlib.sha256(body).hexdigest()}")


def check_stream(directory, name, fields, expected_batches):
    source = (directory / f"{name}.arrows").read_bytes()
    assert len(source) % 8 == 0
    assert source[:4] == b"\xff" * 4 and source[-8:] == b"\xff" * 4 + b"\0" * 4
    with pa.ipc.open_stream(source) as reader:
        assert reader.schema == pa.schema([
            pa.field(field, TYPES[kind][0], nullable=nullable)
            for field, nullable, kind in fields
        ])
        for batch, expected in zip(reader, expected_batches, strict=True):
            batch.validate(full=True)
            assert batch.num_rows == len(expected)
            rows = [tuple(column[row].as_py() for column in batch.columns)
                    for row in range(batch.num_rows)]
            assert rows == expected
    print(f"{name}: batch row counts {[len(rows) for rows in expected_batches]}, "
          f"{len(source)} stream bytes, SHA-256 {hashlib.sha256(source).hexdigest()}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--streams", action="store_true", help="read complete IPC streams")
    args = parser.parse_args()
    assert pa.__version__ == pa.cpp_build_info.version == PRODUCER["version"]
    assert np.__version__ == PRODUCER["numpy_version"]
    if args.streams:
        fields, mixed = CASES["mixed"]
        check_stream(args.directory, "mixed", fields, [mixed, [], mixed])
        fields, empty = CASES["empty"]
        check_stream(args.directory, "empty", fields, [empty])
        fields, zero_columns = CASES["zero-columns"]
        check_stream(args.directory, "zero-columns", fields, [zero_columns, []])
        check_stream(args.directory, "schema-only", [("", False, "utf8")], [])
    else:
        for name, (schema, expected) in CASES.items():
            check(args.directory, name, schema, expected)


if __name__ == "__main__":
    main()
