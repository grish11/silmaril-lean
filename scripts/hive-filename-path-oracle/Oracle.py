"""Differential filename partition checks for pinned PyArrow 26.0.1."""
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

schema = pa.schema([("region", pa.string()), ("year", pa.int32())])
uri = ds.FilenamePartitioning(schema, segment_encoding="uri")
literal = ds.FilenamePartitioning(schema, segment_encoding="none")
leaf = "caf%C3%A9%5fblue_7_A%2Eparquet"
escaped = f"ignored=8/{leaf}"
assigned = "plain/region=west_7_B.parquet"
rejected = "raw/unused_8_C.parquet"
controls = {"nested/_SUCCESS", "_metadata", "_common_metadata"}


def keys(profile, path):
    return ds.get_partition_keys(profile.parse(path))


for profile, region in ((uri, "café_blue"), (literal, "caf%C3%A9%5fblue")):
    assert keys(profile, leaf) == keys(profile, f"dir_9/unrelated/{leaf}") == {"region": region, "year": 7}
    assert keys(profile, "file.parquet") == {}
    assert keys(profile, "west_7") == {"region": "west"}
    assert keys(profile, "west_7_") == {"region": "west", "year": 7}
    assert keys(profile, "west_7_file_name.parquet") == {"region": "west", "year": 7}
    assert keys(profile, "_7_file.parquet") == {"region": "7"}
    assert keys(profile, "%GG_7_file.parquet") == {"region": "%GG", "year": 7}
    assert keys(profile, "nested/_SUCCESS") == keys(profile, "_metadata") == {}
    assert keys(profile, "_common_metadata") == {"region": "common"}
    assert keys(profile, f"../dir//{leaf}") == {"region": region, "year": 7}

assert keys(uri, "x%255Fy_7_tail%GG") == {"region": "x%5Fy", "year": 7}
assert keys(uri, "%5F_SUCCESS") == {"region": "_"}
assert keys(literal, "%5F_SUCCESS") == {"region": "%5F"}
assert keys(literal, "%FF_7_file.parquet") == {"region": "%FF", "year": 7}
try:
    keys(uri, "%FF_7_file.parquet")
except pa.ArrowInvalid:
    pass
else:
    raise AssertionError("URI mode accepted invalid decoded UTF-8")

with tempfile.TemporaryDirectory() as temp:
    root = Path(temp)
    for path in (escaped, assigned, rejected, *sorted(controls)):
        target = root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(b"" if path in controls else payload)
    listing = [rejected, assigned, "nested/_SUCCESS", escaped, escaped, "_metadata", "_common_metadata"]
    ordered = sorted((path for path in listing if path not in controls), key=str.encode)
    for profile, region in ((uri, "café_blue"), (literal, "caf%C3%A9%5fblue")):
        retained = [path for path in ordered if keys(profile, path)["year"] == 7]
        assert retained == [escaped, escaped, assigned]
        dataset = ds.dataset(
            [str(root / path) for path in retained], format="parquet", partitioning=profile,
            partition_base_dir=str(root),
        )
        table = dataset.to_table(columns=["ordinal", "region", "year"], use_threads=False)
        assert table["ordinal"].to_pylist() == [-2147483648, 0, 17, 2147483647, -1] * 3
        assert table["region"].to_pylist() == [region] * 10 + ["region=west"] * 5
        assert table["year"].to_pylist() == [7] * 15
        print(f"Retained {retained!r} with regions {region!r}, {region!r}, 'region=west'")

print("Direct PyArrow parsing interprets _common_metadata as a partial region key. The supplied inventory omits it.")
print("Confirmed last-underscore selection, prefix-only decoding, parent independence and permissive arity controls.")
print(f"CPython {sys.version.split()[0]}, PyArrow {pa.__version__}, NumPy {np.__version__}, fixture {digest}")
