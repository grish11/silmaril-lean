"""Check Lean-written Arrow IPC bodies, streams or files with the pinned PyArrow reader."""
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


def check_batches(schema, batches, fields, expected_batches):
    assert schema == pa.schema([
        pa.field(field, TYPES[kind][0], nullable=nullable)
        for field, nullable, kind in fields
    ])
    for batch, expected in zip(batches, expected_batches, strict=True):
        batch.validate(full=True)
        assert batch.num_rows == len(expected)
        rows = [tuple(column[row].as_py() for column in batch.columns)
                for row in range(batch.num_rows)]
        assert rows == expected


def check_ipc(directory, name, fields, expected_batches, files):
    suffix = "arrow" if files else "arrows"
    source = (directory / f"{name}.{suffix}").read_bytes()
    if files:
        assert source[:8] == b"ARROW1\0\0" and source[-6:] == b"ARROW1"
        size = int.from_bytes(source[-10:-6], "little", signed=True)
        start = len(source) - 10 - size
        assert 0 < size and 8 < start and start % 8 == 0
        assert source[start - 8:start] == b"\xff" * 4 + b"\0" * 4
        with pa.ipc.open_file(source) as reader:
            batches = (reader.get_batch(i) for i in range(reader.num_record_batches))
            check_batches(reader.schema, batches, fields, expected_batches)
    else:
        assert len(source) % 8 == 0
        assert source[:4] == b"\xff" * 4 and source[-8:] == b"\xff" * 4 + b"\0" * 4
        with pa.ipc.open_stream(source) as reader:
            check_batches(reader.schema, reader, fields, expected_batches)
    kind = "file" if files else "stream"
    print(f"{name}: batch row counts {[len(rows) for rows in expected_batches]}, "
          f"{len(source)} {kind} bytes, SHA-256 {hashlib.sha256(source).hexdigest()}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    profiles = parser.add_mutually_exclusive_group()
    profiles.add_argument("--streams", action="store_true", help="read complete IPC streams")
    profiles.add_argument("--files", action="store_true", help="read complete IPC files")
    args = parser.parse_args()
    assert pa.__version__ == pa.cpp_build_info.version == PRODUCER["version"]
    assert np.__version__ == PRODUCER["numpy_version"]
    if args.streams or args.files:
        fields, mixed = CASES["mixed"]
        check_ipc(args.directory, "mixed", fields, [mixed, [], mixed], args.files)
        fields, empty = CASES["empty"]
        check_ipc(args.directory, "empty", fields, [empty], args.files)
        fields, zero_columns = CASES["zero-columns"]
        check_ipc(args.directory, "zero-columns", fields, [zero_columns, []], args.files)
        check_ipc(args.directory, "schema-only", [("", False, "utf8")], [], args.files)
    else:
        for name, (schema, expected) in CASES.items():
            check(args.directory, name, schema, expected)


if __name__ == "__main__":
    main()
