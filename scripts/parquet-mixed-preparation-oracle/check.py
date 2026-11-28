"""Compare the prepared mixed source with its pinned PyArrow/Thrift inputs."""

import argparse
from hashlib import sha256
from importlib.metadata import version
import json
import os
from pathlib import Path
import platform
import subprocess
import sys

import pyarrow as pa
import pyarrow.parquet as pq


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
CASES = (
    ("plain-byte-array-v1.parquet", "payload", [12, 12, 12]),
    ("plain-byte-array-v2.parquet", "payload", [12, 12, 12]),
    ("plain-byte-array-v2-bad-length.parquet", "key", [12, 12, 12]),
    ("empty-middle-v2.parquet", "payload", [3, 0, 2]),
    ("nullable-int32-v2.parquet", "key", [3, 2]),
    ("mixed-schema-only.parquet", "key", []),
)


def extra_sources(out):
    schema = pa.schema([pa.field("ordinal", pa.int32()), pa.field("key", pa.binary(), nullable=False)])
    integer = pa.array([-2**31, None, 0, 2**31 - 1, -1], pa.int32())
    binary = pa.array([b"", b"\xff\x00", b"\x80", b"1234567890123", b"xy"], pa.binary())
    options = dict(version="2.6", data_page_version="2.0", compression="NONE", use_dictionary=False,
                   column_encoding="PLAIN", write_statistics=False, write_page_checksum=False,
                   store_schema=False)
    table = pa.Table.from_arrays([integer, binary], schema=schema)
    pq.write_table(table, out / "nullable-int32-v2.parquet", row_group_size=3, **options)
    with pq.ParquetWriter(out / "mixed-schema-only.parquet", schema, **options):
        pass


def run_generator(script, destination):
    subprocess.run([sys.executable, str(ROOT / script), str(destination)], cwd=ROOT, check=True)


def oracle(out, name, binary, counts):
    with pq.ParquetFile(out / name) as file:
        integer_field = file.schema_arrow.field("ordinal")
        binary_field = file.schema_arrow.field(binary)
        assert integer_field.type == pa.int32() and binary_field.type == pa.binary()
        groups = []
        for index in range(file.num_row_groups):
            batch = file.read_row_group(index, columns=["ordinal", binary], use_threads=False)
            groups.append({
                "rows": batch.num_rows,
                "ints": batch["ordinal"].to_pylist(),
                "bytes": [None if item is None else list(item) for item in batch[binary].to_pylist()],
            })
    assert [group["rows"] for group in groups] == counts
    return {
        "intName": integer_field.name, "intNullable": integer_field.nullable,
        "viewName": binary_field.name, "viewNullable": binary_field.nullable, "groups": groups,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert version("pyarrow") == "26.0.1" and version("thrift") == "0.25.0"
    run_generator("scripts/parquet-plain-byte-array-file/Oracle.py", out)
    run_generator("scripts/parquet-int32-byte-array-group/Check.py", out)
    run_generator("scripts/parquet-int32-byte-array-file/EmptyGroup.py", out / "empty-middle-v2.parquet")
    extra_sources(out)

    pins = json.loads((HERE / "sha256.json").read_text(encoding="utf-8"))
    actual = {name: sha256((out / name).read_bytes()).hexdigest() for name in pins}
    assert actual == pins, actual
    for name, digest in actual.items():
        print(f"{digest}  {name}")

    result = subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
         "-DwarningAsError=true", "--run", str(HERE / "Check.lean"), str(out)],
        cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE,
    )
    observed = json.loads(result.stdout)
    expected = [oracle(out, *case) for case in CASES]
    assert observed == expected, observed
    for name, binary, counts in CASES:
        print(f"PyArrow agrees on the exact INT32 then {binary} descriptors and values for {name} {counts}")
    print("Lean: eight exact cap/selection/read controls with the separate completed prefixes")


if __name__ == "__main__":
    main()
