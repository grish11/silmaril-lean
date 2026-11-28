"""Regenerate the reference IPC files and check the bridge's Parquet outputs."""

import argparse
import hashlib
from pathlib import Path

import pyarrow as pa
import pyarrow.ipc as ipc
import pyarrow.parquet as parquet


SCHEMA = pa.schema([pa.field("café", pa.int32()), pa.field("値", pa.int32())])
FIXTURES = {
    "multi-batch": [[(-(2**31), None), (None, 0)], [], [(2**31 - 1, -1)]],
    "zero-rows": [[]],
}
HASHES = {
    "multi-batch": "05940974fdb06dee126d85ff402cc69aa6c57b9e42dcabe2da2cc78117bb0bb0",
    "zero-rows": "a1f95feaaef32fad2790f760c3b21dd80b2a766c00ac4845138a658254c98308",
}
ROOT = Path(__file__).resolve().parent


def emit_ipc(batches):
    output = pa.BufferOutputStream()
    with ipc.new_stream(output, SCHEMA, options=ipc.IpcWriteOptions(metadata_version=ipc.MetadataVersion.V5)) as stream:
        for rows in batches:
            columns = [pa.array([row[i] for row in rows], type=pa.int32()) for i in range(len(SCHEMA))]
            stream.write_batch(pa.record_batch(columns, schema=SCHEMA))
    return output.getvalue().to_pybytes()


def observe(batches):
    return [dict(zip(SCHEMA.names, row, strict=True)) for rows in batches for row in rows]


def check_ipc(wire, batches):
    with ipc.open_stream(wire) as stream:
        observed = list(stream)
        assert stream.schema == SCHEMA
        assert [batch.num_rows for batch in observed] == [len(batch) for batch in batches]
        assert [row for batch in observed for row in batch.to_pylist()] == observe(batches)


def check_parquet(path, batches):
    with parquet.ParquetFile(path) as source:
        assert source.schema_arrow == SCHEMA
        assert source.num_row_groups == 1
        assert source.metadata.row_group(0).num_rows == sum(map(len, batches))
        assert source.read().to_pylist() == observe(batches)
    print(f"{hashlib.sha256(path.read_bytes()).hexdigest()}  {path.name} (ordered nullable readback)")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--regenerate", action="store_true")
    parser.add_argument("--parquet-dir", type=Path)
    args = parser.parse_args()
    assert pa.__version__ == "26.0.1"
    for name, batches in FIXTURES.items():
        wire = emit_ipc(batches)
        check_ipc(wire, batches)
        digest = hashlib.sha256(wire).hexdigest()
        assert digest == HASHES[name], name
        if name == "multi-batch":
            source = pa.BufferReader(wire)
            for end in (184, 408, 576, 784):
                ipc.read_message(source)
                assert source.tell() == end
            assert source.read() == bytes.fromhex("ffffffff00000000")
        target = ROOT / f"{name}.arrows"
        if args.regenerate:
            target.write_bytes(wire)
        assert target.read_bytes() == wire, target.name
        print(f"{digest}  {target.name} (batches {list(map(len, batches))})")
        if args.parquet_dir is not None:
            check_parquet(args.parquet_dir / f"{name}.parquet", batches)


if __name__ == "__main__":
    main()
