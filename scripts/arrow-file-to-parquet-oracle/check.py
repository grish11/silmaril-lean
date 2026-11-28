"""Produce a checked-reader Arrow IPC file and a late record length control."""
import argparse
from hashlib import sha256
import json
import os
import platform
import subprocess
from pathlib import Path
from struct import pack_into, unpack_from

import pyarrow as pa
import pyarrow.parquet as pq

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SCHEMA = pa.schema([pa.field("n", pa.int32()), pa.field("m", pa.int32())])
BATCHES = [[[-2147483648, None], [0, 17]], [], [[None, -1], [2147483647, None], [-9, 4]]]


def produce(rows_by_batch):
    target = pa.BufferOutputStream()
    options = pa.ipc.IpcWriteOptions(metadata_version=pa.ipc.MetadataVersion.V5, compression=None)
    with pa.ipc.new_file(target, SCHEMA, options=options) as writer:
        for rows in rows_by_batch:
            arrays = [pa.array([row[index] for row in rows], type=pa.int32()) for index in range(len(SCHEMA))]
            writer.write_batch(pa.record_batch(arrays, schema=SCHEMA))
    data = target.getvalue().to_pybytes()
    with pa.ipc.open_file(data) as reader:
        assert reader.schema == SCHEMA
        observed = [reader.get_batch(i).to_pylist() for i in range(reader.num_record_batches)]
        assert observed == [[dict(zip(SCHEMA.names, row)) for row in rows] for rows in rows_by_batch]
    return data


def corrupt_final_record(data):
    changed = bytearray(data)
    offset = 8
    messages = list(pa.ipc.MessageReader.open_stream(data[offset:]))
    assert len(messages) == len(BATCHES) + 1
    for ordinal, message in enumerate(messages):
        marker, size = unpack_from("<II", data, offset)
        assert marker == 0xffffffff and size == message.metadata.size
        metadata = offset + 8
        if ordinal == len(messages) - 1:
            table = metadata + unpack_from("<I", data, metadata)[0]
            vtable = table - unpack_from("<i", data, table)[0]
            field_shift = unpack_from("<H", data, vtable + 4 + 2 * 3)[0]
            assert field_shift and unpack_from("<q", data, table + field_shift)[0] == message.body.size
            pack_into("<q", changed, table + field_shift, 0)
            return bytes(changed), table + field_shift
        offset = metadata + size + (0 if message.body is None else message.body.size)
    raise AssertionError("missing final record")


def fixtures():
    assert pa.__version__ == "26.0.1"
    valid = produce(BATCHES)
    empty = produce([])
    damaged, offset = corrupt_final_record(valid)
    with pa.ipc.open_file(damaged) as reader:
        assert reader.get_batch(0).to_pylist() == [{"n": -2147483648, "m": None}, {"n": 0, "m": 17}]
        assert reader.get_batch(1).num_rows == 0
        try:
            reader.get_batch(2)
        except (pa.ArrowInvalid, OSError):
            pass
        else:
            raise AssertionError("PyArrow accepted the corrupt last block")
    print(f"Last RecordBatch Message bodyLength patched at byte {offset}")
    return {"multi-batch.arrow": valid, "zero-rows.arrow": empty, "late-body-length.arrow": damaged}



def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, required=True)
    output = parser.parse_args().out.resolve()
    output.mkdir(parents=True, exist_ok=True)
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    pins = json.loads((HERE / "pins.json").read_text(encoding="utf-8"))
    sources = []
    for label, wire in fixtures().items():
        digest = sha256(wire).hexdigest()
        assert pins[label] == digest, label
        source = output / label
        source.write_bytes(wire)
        sources.append(str(source))
        print(f"{digest}  {label}")

    targets = [output / f"{name}.parquet" for name in ("multi-batch", "zero-rows")]
    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
         "-DwarningAsError=true", "--run", str(HERE / "Check.lean"), *sources, *map(str, targets)],
        cwd=ROOT, check=True,
    )
    for path, batches in zip(targets, (BATCHES, []), strict=True):
        with pq.ParquetFile(path) as source:
            assert source.schema_arrow == SCHEMA and source.num_row_groups == 1
            assert source.metadata.row_group(0).num_rows == sum(map(len, batches))
            assert source.read().to_pylist() == [
                dict(zip(SCHEMA.names, row, strict=True)) for rows in batches for row in rows
            ]
        print(f"{sha256(path.read_bytes()).hexdigest()}  {path.name} (PyArrow ordered nullable readback)")


if __name__ == "__main__":
    main()
