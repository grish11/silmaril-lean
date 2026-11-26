"""Replay exact-arity positional file paths and PyArrow's broader behavior."""
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
uri = ds.DirectoryPartitioning(schema, segment_encoding="uri")
literal = ds.DirectoryPartitioning(schema, segment_encoding="none")
marker = "__HIVE_DEFAULT_PARTITION__"
alias = "%5f_HIVE_DEFAULT_PARTITION__"
escaped = "caf%C3%A9%2fblue/7/A%2Eparquet"
assigned = "region=west/7/B.parquet"
rejected = "z/8/C.parquet"


def keys(profile, path):
    return ds.get_partition_keys(profile.parse(path))


for profile, marker_alias in ((uri, marker), (literal, alias)):
    assert keys(profile, "west/") == {"region": "west"}
    assert keys(profile, "/") == {}
    assert keys(profile, "west/7/ignored/") == {"region": "west", "year": 7}
    assert keys(profile, f"{marker}/7/") == {"region": marker, "year": 7}
    assert keys(profile, f"{alias}/7/") == {"region": marker_alias, "year": 7}
    assert keys(profile, "%GG/7/") == {"region": "%GG", "year": 7}
    assert profile.format(ds.field("region").is_null()) == ("", "")
    assert profile.format((ds.field("region") == "west") & ds.field("year").is_null()) == ("west", "")
    for rejected_path in ("west//7/", f"west/{marker}/"):
        try:
            keys(profile, rejected_path)
        except pa.ArrowInvalid:
            pass
        else:
            raise AssertionError(f"expected an Int32 cast error: {rejected_path!r}")
    try:
        profile.format(ds.field("region").is_null() & (ds.field("year") == 7))
    except pa.ArrowInvalid:
        pass
    else:
        raise AssertionError("formatter accepted a later key after a null position")

assert keys(ds.DirectoryPartitioning(pa.schema([("region", pa.string()), ("label", pa.string())])),
            "west//extra/") == {"region": "west", "label": ""}
assert keys(literal, "%FF/7/") == {"region": "%FF", "year": 7}
try:
    keys(uri, "%FF/7/")
except pa.ArrowInvalid:
    pass
else:
    raise AssertionError("URI reader accepted invalid decoded UTF-8")

with tempfile.TemporaryDirectory() as temp:
    root = Path(temp)
    for path in (escaped, assigned, rejected):
        target = root / path
        target.parent.mkdir(parents=True)
        target.write_bytes(payload)
    (root / "_metadata").write_bytes(b"")
    listing = [rejected, assigned, "_metadata", escaped, escaped]
    ordered = sorted((path for path in listing if path != "_metadata"), key=str.encode)
    for profile, region in ((uri, "café/blue"), (literal, "caf%C3%A9%2fblue")):
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

print("PyArrow also accepts missing and extra segments, malformed percent text, and empty string slots.")
print("Positional null formatting omits a trailing null and rejects a later key after a null.")
print(f"CPython {sys.version.split()[0]}, PyArrow {pa.__version__}, NumPy {np.__version__}, fixture {digest}")
