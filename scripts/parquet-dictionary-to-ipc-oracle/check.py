"""Verify physical Parquet encodings and the emitted primitive IPC observations."""

import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import platform
from runpy import run_path
import subprocess

import pyarrow as pa
import pyarrow.parquet as pq


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PARQUET = ROOT / "data/parquet-dictionary-snapshot"
SCHEMA = pa.schema([
    pa.field("required_i32", pa.int32(), nullable=False),
    pa.field("optional_i32", pa.int32(), nullable=True),
])


def observe_ipc(wire, expected):
    with pa.ipc.open_stream(wire) as reader:
        assert reader.schema == SCHEMA
        batches = list(reader)
        assert [batch.num_rows for batch in batches] == [batch.num_rows for batch in expected]
        assert batches == expected


def empty_parquet(write_group):
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(
        sink, SCHEMA, version="2.6", data_page_version="2.0", compression="NONE",
        use_dictionary=False, write_statistics=False, write_page_checksum=False,
    ) as writer:
        if write_group:
            writer.write_table(pa.Table.from_batches([], schema=SCHEMA))
    wire = sink.getvalue().to_pybytes()
    with pq.ParquetFile(pa.BufferReader(wire)) as observed:
        assert observed.schema_arrow == SCHEMA
        assert observed.num_row_groups == int(write_group) and observed.read().num_rows == 0
        if write_group:
            group = observed.metadata.row_group(0)
            assert all(group.column(i).data_page_offset == 0 and group.column(i).encodings == ("RLE",)
                       for i in range(group.num_columns))
    return wire


def fixtures():
    oracle = run_path(str(ROOT / "scripts/parquet-dictionary-snapshot/Oracle.py"))
    sources = {
        "mixed-v2.parquet": (1, "UNCOMPRESSED", False),
        "crc-plain-v2.parquet": (1, "UNCOMPRESSED", True),
        "snappy-dictionary-v2.parquet": (0, "SNAPPY", False),
    }
    for label, (dictionary_column, codec, crc) in sources.items():
        oracle["check"](PARQUET / label, dictionary_column, codec, crc)
    print("Thrift: V2 PLAIN data tag 0; PLAIN dictionary tag 0 and RLE_DICTIONARY data tag 8")
    print("Thrift and PyArrow confirmed CRC and Snappy controls")
    with pq.ParquetFile(PARQUET / "mixed-v2.parquet") as source:
        assert source.schema_arrow == SCHEMA
        batches = [source.read_row_group(i).combine_chunks().to_batches()[0]
                   for i in range(source.num_row_groups)]
        assert [batch.num_rows for batch in batches] == [8, 8]

    output = pa.BufferOutputStream()
    options = pa.ipc.IpcWriteOptions(metadata_version=pa.ipc.MetadataVersion.V5, compression=None)
    with pa.ipc.new_stream(output, SCHEMA, options=options) as writer:
        for batch in batches:
            writer.write_batch(batch)
    reference = output.getvalue().to_pybytes()
    observe_ipc(reference, batches)
    mixed = (PARQUET / "mixed-v2.parquet").read_bytes()
    late = mixed[:302] + bytes([33]) + mixed[303:]
    return batches, {
        "mixed-v2.parquet": mixed,
        "invalid-width.parquet": late,
        "reference.arrows": reference,
        "crc-plain-v2.parquet": (PARQUET / "crc-plain-v2.parquet").read_bytes(),
        "snappy-dictionary-v2.parquet": (PARQUET / "snappy-dictionary-v2.parquet").read_bytes(),
        "schema-only.parquet": empty_parquet(write_group=False),
        "empty-pyarrow.parquet": empty_parquet(write_group=True),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    out = parser.parse_args().out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1"
    batches, inputs = fixtures()
    manifest = {name: sha256(wire).hexdigest() for name, wire in inputs.items()}
    assert manifest == json.loads((HERE / "sha256.json").read_text(encoding="utf-8")), manifest
    for name, wire in inputs.items():
        (out / name).write_bytes(wire)
        print(f"{manifest[name]}  {name}")

    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
         "-DwarningAsError=true", "--run", str(HERE / "Check.lean"),
         *[str(out / name) for name in inputs], str(out)],
        cwd=ROOT, check=True,
    )
    with pq.ParquetFile(out / "empty-lean.parquet") as empty:
        assert empty.schema_arrow == SCHEMA and empty.num_row_groups == 1
        assert empty.metadata.row_group(0).num_rows == 0 and empty.read().num_rows == 0
    empty_batch = pa.record_batch([pa.array([], type=pa.int32()) for _ in SCHEMA], schema=SCHEMA)
    for name, expected in [
        ("mixed-output.arrows", batches),
        ("schema-only-output.arrows", []),
        ("empty-output.arrows", [empty_batch]),
    ]:
        wire = (out / name).read_bytes()
        observe_ipc(wire, expected)
        print(f"{sha256(wire).hexdigest()}  {name} (PyArrow batches {[batch.num_rows for batch in expected]})")


if __name__ == "__main__":
    main()
