"""Verify the raw Hive segment profile and producer ambiguity in PyArrow 26.0.1."""
import hashlib
from pathlib import Path
import sys
import tempfile

import numpy as np
import pyarrow as pa
import pyarrow.dataset as ds

assert sys.version_info[:3] == (3, 14, 7)
assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
assert np.__version__ == "2.5.5"

fixture = Path(sys.argv[1])
payload = fixture.read_bytes()
digest = hashlib.sha256(payload).hexdigest()
assert digest == "4417fe68ce84210af4979a2f7ef19d05764fc3ce3bf71f83b25b546658e76f48"
schema = pa.schema([("label", pa.string())])
literal = ds.HivePartitioning(schema, segment_encoding="none")
uri = ds.HivePartitioning(schema, segment_encoding="uri")
marker = "__HIVE_DEFAULT_PARTITION__"
alias = "%5f_HIVE_DEFAULT_PARTITION__"

with tempfile.TemporaryDirectory() as temp:
    root = Path(temp)
    for raw, literal_value, uri_value in (
        (marker, None, None),
        (alias, alias, None),
        ("caf%C3%A9%2fblue", "caf%C3%A9%2fblue", "café/blue"),
        ("café", "café", "café"),
        ("", "", ""),
    ):
        relative = f"label={raw}/f%2eparquet"
        file = root / relative
        file.parent.mkdir()
        file.write_bytes(payload)
        for profile, expected in ((literal, literal_value), (uri, uri_value)):
            dataset = ds.dataset([str(file)], format="parquet", partitioning=profile,
                                 partition_base_dir=str(root))
            assert dataset.to_table(columns=["label"], use_threads=False)["label"].to_pylist() == [expected] * 5
        print(f"{relative} gives literal={literal_value!r}, URI={uri_value!r}")

assert ds.get_partition_keys(literal.parse("label=%FF/")) == {"label": "%FF"}
assert ds.get_partition_keys(literal.parse("label=a+b=c/")) == {"label": "a+b=c"}

for profile in (literal, uri):
    null_path = profile.format(ds.field("label").is_null())
    sentinel_path = profile.format(ds.field("label") == marker)
    assert null_path == sentinel_path == (f"label={marker}", "")
    assert ds.get_partition_keys(profile.parse(null_path[0] + "/")) == {"label": None}

assert literal.format(ds.field("label") == alias) == ("label=%255f_HIVE_DEFAULT_PARTITION__", "")
print(f"The producer formats both null and literal sentinel text as label={marker}; raw-mode formatting still URI-escapes.")
print(f"CPython {sys.version.split()[0]}, PyArrow {pa.__version__}, NumPy {np.__version__}, fixture {digest}")
