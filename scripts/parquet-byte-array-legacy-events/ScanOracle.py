"""Decode both original legacy leaves independently and exercise logical scans."""
from importlib.metadata import version
from pathlib import Path

import pyarrow.parquet as pq

assert version("pyarrow") == "26.0.1"
root = Path(__file__).resolve().parents[2]
fixtures = root / "data/parquet-byte-array-legacy-events"


def int_predicate(ordinal, _payload):
    return ordinal % 13 == 5 or ordinal % 64 == 0


def binary_predicate(_ordinal, payload):
    return payload is not None and len(payload) > 8


def cell(value):
    if value is None:
        return "-"
    return value.hex() if isinstance(value, bytes) else str(value)


def scan(groups, keep, columns):
    lines = []
    for group in groups:
        selected = [row for row in group if keep(*row)]
        lines.append(f"batch {len(selected)}")
        if columns:
            lines.extend(",".join(cell(row[i]) for i in columns) for row in selected)
    return lines


def read(path, damaged):
    with pq.ParquetFile(path) as file:
        assert [file.metadata.row_group(i).num_rows for i in range(3)] == [384, 0, 384]
        groups = [
            list(zip(batch["ordinal"].to_pylist(), batch["payload"].to_pylist(), strict=True))
            for batch in (file.read_row_group(i, columns=["ordinal", "payload"]) for i in range(2 if damaged else 3))
        ]
        if damaged:
            try:
                file.read_row_group(2, columns=["ordinal", "payload"])
            except (OSError, ValueError):
                pass
            else:
                raise AssertionError("PyArrow admitted the damaged last group")
        return groups


clean = read(fixtures / "legacy-v1-empty-middle.parquet", False)
damaged = read(fixtures / "legacy-v1-late-error.parquet", True)
assert clean[:2] == damaged
for label, groups in (("clean", clean), ("damaged", damaged)):
    for name, keep, columns in (
        ("ordinal to payload", int_predicate, [1]),
        ("payload to ordinal", binary_predicate, [0]),
        ("reorder and repeat", int_predicate, [1, 0, 1]),
        ("zero columns", binary_predicate, []),
        ("unknown", lambda _ordinal, _payload: False, []),
    ):
        print(f"{label} {name}")
        print("\n".join(scan(groups, keep, columns)))
