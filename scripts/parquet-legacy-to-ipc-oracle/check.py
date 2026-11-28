"""Read native IPC from the paired legacy Parquet source with pinned PyArrow."""

from hashlib import sha256
from importlib.metadata import version
import os
from pathlib import Path
from runpy import run_path
import subprocess
import sys

import pyarrow as pa
import pyarrow.parquet as pq

assert version("pyarrow") == "26.0.1"
here = Path(__file__).resolve().parent
root = here.parents[1]
verify_ipc = run_path(str(root / "scripts/parquet-mixed-to-ipc-oracle/check.py"))["verify_ipc"]
fixtures = root / "data/parquet-byte-array-legacy-events"
original = (fixtures / "legacy-v1-empty-middle.parquet").read_bytes()
damaged = (fixtures / "legacy-v1-late-error.parquet").read_bytes()
assert sha256(original).hexdigest() == "67a4029e7ff4afcd9e3c88e1a335d22e4c52ef9d16ebd9e324b61e935d1e91a5"
assert sha256(damaged).hexdigest() == "58a6f17e3547e743c6dad6c66d4306a9f843875ecb438862bbd36e0c44036a77"

# Same-length edits retain the original dictionary reference runs, page
# headers, null definitions, PLAIN length word and footer offsets.
opaque = bytearray(original)
assert opaque[1917:1925] == b"repeat-a"
assert opaque[21040:21056] == b"distinct-0372-op"
opaque[1917:1919] = b"\xff\x00"
opaque[21040:21042] = b"\x00\xfe"
assert sha256(opaque).hexdigest() == "1500f05bd60795fdd40fa2ab3347b9bfa6b69388c731ea7be926cfc72b8fc29f"

out = Path(sys.argv[1]).resolve()
out.mkdir(parents=True, exist_ok=True)
for name, wire in (("original", original), ("opaque", opaque), ("damaged", damaged)):
    (out / f"{name}.parquet").write_bytes(wire)

with pq.ParquetFile(out / "damaged.parquet") as source:
    assert [source.read_row_group(i).num_rows for i in range(2)] == [384, 0]
    try:
        source.read_row_group(2)
    except (OSError, ValueError):
        pass
    else:
        raise AssertionError("PyArrow admitted the late length damage")

subprocess.run(
    [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
     "--run", str(here / "Check.lean"), str(out)], cwd=root, check=True,
)
assert not (out / "damaged.arrows").exists()

for name in ("original", "opaque"):
    with pq.ParquetFile(out / f"{name}.parquet") as source:
        assert source.schema_arrow == pa.schema([
            pa.field("ordinal", pa.int32(), nullable=False),
            pa.field("payload", pa.binary(), nullable=True),
        ])
        table = {"intName": "ordinal", "intNullable": False, "viewName": "payload", "viewNullable": True,
                 "groups": []}
        for i in range(source.num_row_groups):
            batch = source.read_row_group(i)
            table["groups"].append({"rows": batch.num_rows, "ints": batch["ordinal"].to_pylist(),
                                    "bytes": batch["payload"].to_pylist()})
        assert [group["rows"] for group in table["groups"]] == [384, 0, 384]
        assert table["groups"][0]["bytes"][5] is None
        if name == "opaque":
            assert table["groups"][0]["bytes"][0] == b"\xff\x00peat-a"
            assert table["groups"][2]["bytes"][372].startswith(b"\x00\xfe")
    wire = (out / f"{name}.arrows").read_bytes()
    verify_ipc(wire, table)
    print(f"{sha256(wire).hexdigest()}  {name}.arrows (exact V5 fields, octets, [384, 0, 384], EOS)")
print(f"{sha256(opaque).hexdigest()}  opaque.parquet (same-length non-UTF8 control)")
