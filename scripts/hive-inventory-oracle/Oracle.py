"""Independent Hive inventory fixture using pinned PyArrow 26.0.1."""
import hashlib
import json
from pathlib import Path
import sys

import numpy as np
import pyarrow as pa
import pyarrow.dataset as ds
import pyarrow.parquet as pq

assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
assert np.__version__ == "2.5.5"
root = Path(sys.argv[1])
root.mkdir(parents=True, exist_ok=True)
physical = pa.schema([pa.field("value", pa.int32(), nullable=False)])
partitions = ds.HivePartitioning(
    pa.schema([pa.field("year", pa.int32())]), segment_encoding="uri",
)
escaped = "year=%37/part-a.parquet"
null_partition = "year=__HIVE_DEFAULT_PARTITION__/part-null.parquet"
other = "year=9/part-b.parquet"
metadata = []
for declared, value in [(escaped, 10), (null_partition, 20), (other, 30)]:
    path = root / declared
    path.parent.mkdir(parents=True, exist_ok=True)
    table = pa.Table.from_arrays([pa.array([value], type=pa.int32())], schema=physical)
    pq.write_table(
        table, path, version="2.6", data_page_version="1.0", compression="NONE",
        use_dictionary=False, write_statistics=False, write_page_checksum=False,
        metadata_collector=metadata,
    )
    metadata[-1].set_file_path(declared)

(root / "_SUCCESS").write_bytes(b"")
pq.write_metadata(physical, root / "_metadata", metadata_collector=metadata)
pq.write_metadata(physical, root / "_common_metadata")
assert [pq.read_metadata(root / "_metadata").row_group(i).column(0).file_path
        for i in range(3)] == [escaped, null_partition, other]

inventory = ["_SUCCESS", escaped, "_metadata", null_partition, escaped, "_common_metadata", other]
discovered = ds.dataset(root, format="parquet", partitioning=partitions, exclude_invalid_files=False)
selected_set = {
    Path(fragment.path).relative_to(root).as_posix() for fragment in discovered.get_fragments()
}
assert selected_set == {escaped, null_partition, other}
selected = [path for path in inventory if path in selected_set]
assert selected == [escaped, null_partition, escaped, other]

# The producer's directory scan determines membership. Explicit paths restore
# the supplied order and repeat the escaped declaration.
explicit = ds.dataset(
    [str(root / path) for path in selected], format="parquet", partitioning=partitions,
    partition_base_dir=str(root), exclude_invalid_files=False,
)
rows = explicit.to_table(use_threads=False).to_pylist()
assert rows == [
    {"value": 10, "year": 7},
    {"value": 20, "year": None},
    {"value": 10, "year": 7},
    {"value": 30, "year": 9},
]
# Directory discovery establishes membership. Caller-side bytewise ordering
# defines the successful manifest even if the listing arrives reversed.
permuted_inventory = list(reversed(inventory))
ordered_paths = sorted((path for path in permuted_inventory if path in selected_set), key=str.encode)
assert ordered_paths == [escaped, escaped, other, null_partition]
ordered_dataset = ds.dataset(
    [str(root / path) for path in ordered_paths], format="parquet", partitioning=partitions,
    partition_base_dir=str(root), exclude_invalid_files=False,
)
ordered_rows = ordered_dataset.to_table(use_threads=False).to_pylist()
assert ordered_rows == [
    {"value": 10, "year": 7},
    {"value": 10, "year": 7},
    {"value": 30, "year": 9},
    {"value": 20, "year": None},
]

try:
    ds.dataset(
        [str(root / path) for path in inventory], format="parquet", partitioning=partitions,
        partition_base_dir=str(root), exclude_invalid_files=False,
    ).to_table(use_threads=False)
except (pa.ArrowException, OSError) as error:
    assert "_SUCCESS" in str(error), str(error)
    explicit_unfiltered = {"type": type(error).__name__, "path": "_SUCCESS"}
else:
    raise AssertionError("unfiltered explicit inventory unexpectedly yielded rows")

paths = sorted(set(inventory))
observation = {
    "cpython": sys.version.split()[0],
    "pyarrow": pa.__version__,
    "numpy": np.__version__,
    "inventory": inventory,
    "directory_discovered": sorted(selected_set),
    "selected_occurrences": selected,
    "ordered_typed_rows": rows,
    "lexical_occurrences": ordered_paths,
    "lexical_rows": ordered_rows,
    "unfiltered_explicit_inventory_error": explicit_unfiltered,
    "sha256": {path: hashlib.sha256((root / path).read_bytes()).hexdigest() for path in paths},
}
print(json.dumps(observation, indent=2, ensure_ascii=False))
