"""Read actual Lean-rendered filenames using pinned PyArrow."""
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
metadata = pq.read_metadata(fixture)
assert [metadata.row_group(i).num_rows for i in range(metadata.num_row_groups)] == [3, 0, 2]
names = Path(sys.argv[2]).read_text(encoding="utf-8").splitlines()
assert names == [
    "a%5Fb_7_part-0.parquet", "caf%C3%A9%2Fx%255F_8_part-1.parquet",
    "café%5f_7_part-2.parquet", "part-3.parquet",
]
schema = pa.schema([("region", pa.string()), ("year", pa.int32())])
uri = ds.FilenamePartitioning(schema, segment_encoding="uri")
literal = ds.FilenamePartitioning(schema, segment_encoding="none")
zero = ds.FilenamePartitioning(pa.schema([]))

with tempfile.TemporaryDirectory() as temp:
    root = Path(temp)
    parent = root / "ignored=parent"
    parent.mkdir()
    files = [parent / name for name in names]
    for file in files:
        file.write_bytes(payload)

    for profile, selected, values in (
        (uri, [files[0], files[1], files[0]], [("a_b", 7), ("café/x%5F", 8), ("a_b", 7)]),
        (literal, [files[2]], [("café%5f", 7)]),
        (zero, [files[3]], []),
    ):
        dataset = ds.dataset([str(file) for file in selected], format="parquet",
                             partitioning=profile, partition_base_dir=str(root))
        columns = ["ordinal", "region", "year"] if values else ["ordinal"]
        table = dataset.to_table(columns=columns, use_threads=False)
        assert table["ordinal"].to_pylist() == [-2147483648, 0, 17, 2147483647, -1] * len(selected)
        if values:
            assert table["region"].to_pylist() == [region for region, _ in values for _ in range(5)]
            assert table["year"].to_pylist() == [year for _, year in values for _ in range(5)]
        print(f"{[file.name for file in selected]!r}: exact readback {values!r}")

assert uri.format((ds.field("region") == "a_b") & (ds.field("year") == 7)) == ("", "a_b_7_")
print("PyArrow's own formatter leaves the underscore in the value raw.")
print(f"CPython {sys.version.split()[0]}, PyArrow {pa.__version__}, NumPy {np.__version__}, fixture {digest}")
