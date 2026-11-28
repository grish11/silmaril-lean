"""Pair pinned Parquet selections with independently emitted PyArrow IPC."""

import argparse
from hashlib import sha256
import os
from pathlib import Path
from runpy import run_path
import subprocess
import sys

import pyarrow as pa


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SOURCE = ROOT / "scripts/parquet-mixed-preparation-oracle/check.py"
PINS = {
    "coalesced": "0cfda713cdd2019609aa114108356319d1108b67aef57bf0045b3762961a809f",
    "explicit-empty": "488c597c53bc9ffb2753a7a835e3789c1a212af26fb21b98b5a960305e2c39e6",
    "null-to-empty": "9b4163ee085c539eefb35e76248821b46cba93738266a929d530e183d6f378d3",
    "reordered": "30858b0e0e50d628c3ac2f2f3984fbe3862221e89df0b9129f6051544ff6f673",
    "resplit": "990bf86001c1e48facfeb1cfa69b8cff624548c56c9aca9303e19d3da898af3a",
}


def pairs(table):
    return [(integer, None if octets is None else bytes(octets))
            for group in table["groups"]
            for integer, octets in zip(group["ints"], group["bytes"], strict=True)]


def stream(out, name, table, rows, sizes):
    assert sum(sizes) == len(rows)
    schema = pa.schema([
        pa.field(table["intName"], pa.int32(), nullable=table["intNullable"]),
        pa.field(table["viewName"], pa.binary_view(), nullable=table["viewNullable"]),
    ])
    options = pa.ipc.IpcWriteOptions(metadata_version=pa.ipc.MetadataVersion.V5,
                                     use_legacy_format=False, compression=None)
    sink = pa.BufferOutputStream()
    with pa.ipc.new_stream(sink, schema, options=options) as writer:
        offset = 0
        for size in sizes:
            batch = rows[offset:offset + size]
            writer.write_batch(pa.record_batch(
                [pa.array([row[index] for row in batch], type=field.type)
                 for index, field in enumerate(schema)], schema=schema))
            offset += size

    wire = sink.getvalue().to_pybytes()
    assert wire.endswith(bytes.fromhex("ffffffff00000000"))
    with pa.BufferReader(wire) as carrier, pa.ipc.open_stream(carrier) as reader:
        assert reader.schema.equals(schema)
        batches = list(reader)
        assert [batch.num_rows for batch in batches] == sizes
        for batch in batches:
            batch.validate(full=True)
        assert [row for batch in batches for row in
                zip(*(column.to_pylist() for column in batch.columns), strict=True)] == rows
        assert carrier.tell() == len(wire)

    digest = sha256(wire).hexdigest()
    print(f"{digest}  {name}.arrows {sizes}", flush=True)
    assert digest == PINS[name], f"{name}: fixture hash changed"
    (out / f"{name}.arrows").write_bytes(wire)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    out = parser.parse_args().out.resolve()
    subprocess.run([sys.executable, str(SOURCE), "--out", str(out)], cwd=ROOT, check=True)
    oracle = run_path(str(SOURCE))["oracle"]
    middle = oracle(out, "empty-middle-v2.parquet", "payload", [3, 0, 2])
    nullable = oracle(out, "nullable-int32-v2.parquet", "key", [3, 2])
    empty = oracle(out, "mixed-schema-only.parquet", "key", [])
    rows = pairs(middle)
    assert rows[0][1] is None and rows[1][1] == b""
    stream(out, "coalesced", middle, rows, [5])
    stream(out, "resplit", nullable, pairs(nullable), [0, 1, 4])
    stream(out, "explicit-empty", empty, pairs(empty), [0])
    stream(out, "reordered", middle, [rows[1], rows[0], *rows[2:]], [5])
    stream(out, "null-to-empty", middle, [(rows[0][0], b""), *rows[1:]], [5])
    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
         "-DwarningAsError=true", "--run", str(HERE / "Check.lean"), str(out)],
        cwd=ROOT, check=True,
    )


if __name__ == "__main__":
    main()
