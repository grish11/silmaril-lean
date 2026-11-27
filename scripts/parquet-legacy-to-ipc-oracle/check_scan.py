"""Compare native IPC projections with independently filtered PyArrow Parquet groups."""

from hashlib import sha256
from importlib.metadata import version
import os
from pathlib import Path
import subprocess
import sys

import pyarrow as pa
import pyarrow.parquet as pq

assert version("pyarrow") == "26.0.1"
here = Path(__file__).resolve().parent
root = here.parents[1]
out = Path(sys.argv[1]).resolve()
subprocess.run([sys.executable, str(here / "check.py"), str(out)], cwd=root, check=True)
subprocess.run(
    [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
     "--run", str(here / "Scan.lean"), str(out)], cwd=root, check=True,
)

assert not list(out.glob("damaged-*.arrows"))

ordinal = pa.field("ordinal", pa.int32(), nullable=False)
payload = pa.field("payload", pa.binary_view(), nullable=True)


def by_ordinal(integer, _):
    return integer % 13 == 5 or integer % 64 == 0 or integer == 372


def by_payload(_, blob):
    return blob is not None and len(blob) > 8


cases = [
    ("payload-by-ordinal", [1], by_ordinal),
    ("ordinal-by-payload", [0], by_payload),
    ("reordered", [1, 0], by_ordinal),
    ("paired-by-payload", [0, 1], by_payload),
    ("repeated-int32", [0, 0], by_payload),
    ("zero-width", [], by_payload),
    ("discard-all", [1, 0], lambda *_: False),
]

for name in ("original", "opaque"):
    with pq.ParquetFile(out / f"{name}.parquet") as source:
        groups = [
            list(zip(group["ordinal"].to_pylist(), group["payload"].to_pylist(), strict=True))
            for group in (source.read_row_group(i) for i in range(source.num_row_groups))
        ]
    for label, projection, keep in cases:
        expected_schema = pa.schema([(ordinal, payload)[index] for index in projection])
        expected_batches = []
        for rows in groups:
            survivors = [row for row in rows if keep(*row)]
            if projection:
                columns = [
                    pa.array([row[index] for row in survivors], type=field.type)
                    for index, field in zip(projection, expected_schema, strict=True)
                ]
                expected_batches.append(pa.record_batch(columns, schema=expected_schema))
            else:
                # Selecting no columns from an existing batch retains cardinality.
                expected_batches.append(pa.record_batch([pa.nulls(len(survivors))], names=["unused"]).select([]))
        counts = [batch.num_rows for batch in expected_batches]
        assert len(counts) == 3 and counts[1] == 0
        if label == "discard-all":
            assert counts == [0, 0, 0]
        else:
            assert counts[0] > 0 and counts[2] > 0
        if label == "payload-by-ordinal":
            assert None in expected_batches[0].column(0).to_pylist()
            if name == "opaque":
                assert b"\xff\x00peat-a" in expected_batches[0].column(0).to_pylist()
                assert any(value is not None and value.startswith(b"\x00\xfe")
                           for value in expected_batches[2].column(0).to_pylist())
        filename = f"{name}-{label}.arrows"
        wire = (out / filename).read_bytes()
        assert wire[-8:] == b"\xff\xff\xff\xff\x00\x00\x00\x00"
        carrier = pa.BufferReader(wire)
        with pa.ipc.open_stream(carrier) as reader:
            assert reader.schema.equals(expected_schema, check_metadata=True)
            for batch, expected in zip(reader, expected_batches, strict=True):
                assert batch.num_rows == expected.num_rows
                assert batch.equals(expected, check_metadata=True)
            assert carrier.tell() == len(wire)
        print(f"{sha256(wire).hexdigest()}  {filename}  {counts}")
