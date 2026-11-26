"""Replay supplied Hive paths against an existing pinned Parquet fixture."""
import hashlib
from pathlib import Path
import sys
import tempfile

import numpy as np
import pyarrow as pa
import pyarrow.dataset as ds
import pyarrow.parquet as pq

assert sys.version_info[:3] == (3, 14, 7)
assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
assert np.__version__ == "2.5.5"

fixture = Path(sys.argv[1])
payload = fixture.read_bytes()
digest = hashlib.sha256(payload).hexdigest()
assert digest == "4417fe68ce84210af4979a2f7ef19d05764fc3ce3bf71f83b25b546658e76f48"
footer = pq.read_metadata(fixture)
assert [footer.row_group(i).num_rows for i in range(footer.num_row_groups)] == [3, 0, 2]

spec = pa.schema([("year", pa.int32()), ("label", pa.string())])
partitioning = ds.HivePartitioning(spec, segment_encoding="uri")
paths = [
    ("label=caf%C3%A9%2fblue/year=-2147483648/lower%2Eparquet", -2147483648, b"caf\xc3\xa9/blue"),
    ("label=%5F_HIVE_DEFAULT_PARTITION__/year=__HIVE_DEFAULT_PARTITION__/null.parquet", None, None),
    ("year=2147483647/label=/upper.parquet", 2147483647, b""),
    ("label=__HIVE_DEFAULT_PARTITION__/missing.parquet", None, None),
]

with tempfile.TemporaryDirectory() as temp:
    root = Path(temp)
    for path, year, label in paths:
        actual = root / path
        actual.parent.mkdir(parents=True, exist_ok=True)
        actual.write_bytes(payload)
        table = ds.dataset(
            [str(actual)], format="parquet", partitioning=partitioning,
            partition_base_dir=str(root),
        ).to_table(columns=spec.names, use_threads=False)
        assert table.schema == spec
        labels = [None if value is None else value.encode("utf-8") for value in table["label"].to_pylist()]
        assert labels == [label] * 5
        assert table["year"].to_pylist() == [year] * 5
        print(f"{path}: {(year, label)!r} over five rows")

for text in ("2147483648", "-2147483649", "1.5", "1_0"):
    try:
        partitioning.parse(f"year={text}/")
    except pa.ArrowInvalid:
        print(f"Rejected INT32 path value {text!r}")
    else:
        raise AssertionError(f"Accepted out-of-profile INT32 path value {text!r}")

print(f"CPython {sys.version.split()[0]}, PyArrow {pa.__version__}, NumPy {np.__version__}")
print(f"{fixture.name}: {digest}, group sizes [3, 0, 2]")
