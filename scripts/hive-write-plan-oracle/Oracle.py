"""Pinned PyArrow directory and row membership for Hive write planning."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys

import numpy as np
import pyarrow as pa
import pyarrow.dataset as ds
import pyarrow.parquet as pq

assert sys.version_info[:3] == (3, 14, 7)
assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
assert np.__version__ == "2.5.5"

root = Path(sys.argv[1])
partition_schema = pa.schema([("region", pa.string()), ("year", pa.int32())])
schema = pa.schema([
    pa.field("id", pa.int32(), nullable=False),
    pa.field("amount", pa.int32()),
    *partition_schema,
])
rows = [
    (10, None, "a/b", 2025),
    (20, 4, None, 2025),
    (11, 8, "a/b", 2025),
    (30, 9, "日本", 2024),
    (40, None, "", 2025),
    (21, None, None, 2025),
    (50, 2, "x=y", None),
    (10, None, "a/b", 2025),
]
expected = [
    ("region=a%2Fb/year=2025", [(10, None), (11, 8), (10, None)]),
    ("region=__HIVE_DEFAULT_PARTITION__/year=2025", [(20, 4), (21, None)]),
    ("region=%E6%97%A5%E6%9C%AC/year=2024", [(30, 9)]),
    ("region=/year=2025", [(40, None)]),
    ("region=x%3Dy/year=__HIVE_DEFAULT_PARTITION__", [(50, 2)]),
]
partitioning = ds.partitioning(partition_schema, flavor="hive")
parquet = ds.ParquetFileFormat()
options = parquet.make_write_options(
    version="2.6", compression="NONE", use_dictionary=False,
    data_page_version="1.0", write_statistics=False, write_page_checksum=False,
)

def write_dataset(path, values):
    table = pa.Table.from_pylist([dict(zip(schema.names, row, strict=True)) for row in values], schema=schema)
    ds.write_dataset(
        table, path, format=parquet, file_options=options, partitioning=partitioning,
        use_threads=False, preserve_order=True, basename_template="part-{i}.parquet",
    )

normal = root / "data"
write_dataset(normal, rows)
paths = [normal / directory / "part-0.parquet" for directory, _ in expected]
assert sorted(normal.rglob("*.parquet")) == sorted(paths)
for path, (_, expected_cells) in zip(paths, expected, strict=True):
    physical = pq.ParquetFile(path).read()
    assert physical.schema == pa.schema(list(schema)[:2])
    assert Counter((r["id"], r["amount"]) for r in physical.to_pylist()) == Counter(expected_cells)

# Verify logical membership including duplicates. The Lean checks specify
# ordering over the same rows independently of PyArrow enumeration.
dataset = ds.dataset(
    [str(p) for p in paths], format=parquet, schema=schema, partitioning=partitioning,
    partition_base_dir=str(normal), exclude_invalid_files=False,
)
readback = dataset.to_table(use_threads=False).to_pylist()
assert Counter(tuple(row[name] for name in schema.names) for row in readback) == Counter(rows)

print(json.dumps({
    "cpython": sys.version.split()[0],
    "pyarrow": pa.__version__,
    "numpy": np.__version__,
    "input_rows": rows,
    "directory_membership": dict(expected),
    "logical_row_membership_matches_input": True,
    "sha256": {p.relative_to(root).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
               for p in sorted(root.rglob("*.parquet"))},
}, ensure_ascii=False, indent=2))
