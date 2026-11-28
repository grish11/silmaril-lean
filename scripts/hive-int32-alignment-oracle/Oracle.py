"""Reproduce mixed Hive Parquet physical schemas with PyArrow 26.0.1."""
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
old = "year=%37/base.parquet"
new = "year=__HIVE_DEFAULT_PARTITION__/added.parquet"
bad = "year=8/damaged.parquet"

identifier = pa.field("id", pa.int32(), nullable=False)
latency = pa.field("latency", pa.int32())

def write(path, schema, values):
    destination = root / path
    destination.parent.mkdir(parents=True, exist_ok=True)
    table = pa.Table.from_arrays(
        [pa.array(value, type=field.type) for value, field in zip(values, schema, strict=True)],
        schema=schema,
    )
    pq.write_table(
        table, destination, version="2.6", data_page_version="1.0", compression="NONE",
        use_dictionary=False, write_statistics=False, write_page_checksum=False,
        row_group_size=1,
    )

write(old, pa.schema([identifier]), [[10, 11]])
write(new, pa.schema([latency, identifier]), [[200, None], [20, 21]])
physical_names = {path: pq.read_schema(root / path).names for path in (old, new)}
assert physical_names == {old: ["id"], new: ["latency", "id"]}
assert all(pq.read_metadata(root / path).num_row_groups == 2 for path in (old, new))

year = pa.field("year", pa.int32())
target = pa.schema([identifier, latency, year])
partitioning = ds.HivePartitioning(pa.schema([year]), segment_encoding="uri")
paths = [old, new, old]
dataset = ds.dataset(
    [str(root / path) for path in paths], format="parquet", schema=target,
    partitioning=partitioning, partition_base_dir=str(root), exclude_invalid_files=False,
)
table = dataset.to_table(use_threads=False)
assert table.schema == target
rows = [tuple(row[column] for column in target.names) for row in table.to_pylist()]
assert rows == [
    (10, None, 7), (11, None, 7),
    (20, 200, None), (21, None, None),
    (10, None, 7), (11, None, 7),
]
# Leave the footer and group 0 intact. Make the first column's group-1
# Compact PageHeader stop before declaring any required fields.
offset = pq.read_metadata(root / new).row_group(1).column(0).data_page_offset
physical_bytes = (root / new).read_bytes()
damaged = root / bad
damaged.parent.mkdir(parents=True, exist_ok=True)
damaged.write_bytes(physical_bytes[:offset] + b"\x00" + physical_bytes[offset + 1:])
reader = pq.ParquetFile(damaged)
assert reader.read_row_group(0).to_pylist() == [{"latency": 200, "id": 20}]
try:
    reader.read_row_group(1)
except (pa.ArrowInvalid, OSError) as error:
    assert "page header" in str(error).lower()
else:
    raise AssertionError("damaged second group unexpectedly decoded")

print(json.dumps({
    "cpython": sys.version.split()[0],
    "pyarrow": pa.__version__,
    "numpy": np.__version__,
    "paths": paths,
    "physical_names": physical_names,
    "target_names": table.schema.names,
    "ordered_rows": rows,
    "damaged_page_header_offset": offset,
    "sha256": {path: hashlib.sha256((root / path).read_bytes()).hexdigest()
               for path in (old, new, bad)},
}, indent=2))
