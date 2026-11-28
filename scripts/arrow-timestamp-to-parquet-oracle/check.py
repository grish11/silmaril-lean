"""Pin PyArrow TIMESTAMP IPC inputs and check native Lean Parquet output."""

from hashlib import sha256
from importlib.metadata import version
import json
import os
from pathlib import Path
import platform
import runpy
import struct
import subprocess
import tempfile

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

ROOT = Path(__file__).resolve().parents[2]
ARROW = runpy.run_path(str(ROOT / "tests/formats/arrow-timestamp-stream/check-fixtures.py"))
THRIFT = runpy.run_path(str(ROOT / "tests/formats/parquet-timestamp-leaf/check-fixtures.py"))
MIN, MAX = -(2**63), 2**63 - 1
PIN = "34d8157141f1f53674602e26e2dd263296f197b83057f91287b87861022b55b8"


def cases():
    for unit in ("ms", "us", "ns"):
        for timezone in (None, "UTC"):
            name = unit + ("_utc" if timezone else "_local")
            nullable = name != "ns_utc"
            rows = [[MIN, None if nullable else -2, -1], [], [], [0, MAX, 17]]
            yield name, ARROW["timestamp_stream"](unit, timezone, rows, nullable)
    yield "schema_only", ARROW["timestamp_stream"]("us", None, [], False)
    # Missing EOS makes every unsupported descriptor a test of early refusal.
    yield "seconds", ARROW["timestamp_stream"]("s", None, [[1]])[:-8]
    zoned = ARROW["timestamp_stream"]("ns", "Asia/Kathmandu", [[-1], []])
    yield "named", zoned[:-8]
    yield "empty_timezone", ARROW["explicit_empty_timezone"](zoned)[:-8]
    yield "offset", ARROW["timestamp_stream"]("us", "+00:00", [[-1]])[:-8]
    yield "missing_eos", ARROW["timestamp_stream"]("us", None, [[MIN], [], [], [MAX]])[:-8]


def footer(wire):
    size, = struct.unpack_from("<I", wire, len(wire) - 8)
    source = TMemoryBuffer(wire[-8-size:-8])
    result = THRIFT["read_struct"](TCompactProtocol(source))
    assert source.cstringio_buf.tell() == size
    return result


def verify(source, wire):
    reader = pa.ipc.open_stream(source)
    field = reader.schema.field(0)
    batches = [batch.column(0).cast(pa.int64()).to_pylist() for batch in reader]
    parquet = pq.ParquetFile(pa.BufferReader(wire))
    assert parquet.schema_arrow.field(0).equals(field, check_metadata=True)
    assert parquet.schema.column(0).physical_type == "INT64"
    logical = json.loads(parquet.schema.column(0).logical_type.to_json())
    assert logical["Type"] == "Timestamp" and logical["isAdjustedToUTC"] == (field.type.tz == "UTC")
    assert parquet.metadata.num_row_groups == len(batches)
    assert parquet.metadata.num_rows == sum(map(len, batches))
    metadata = footer(wire)
    schema_leaf = THRIFT["list_field"](metadata, 2)[1]
    assert [group[3][1] for group in THRIFT["list_field"](metadata, 4)] == list(map(len, batches))
    assert schema_leaf[1][1] == 2
    converted = {"ms": 9, "us": 10}.get(field.type.unit)
    assert (schema_leaf[6][1] if 6 in schema_leaf else None) == converted
    timestamp = schema_leaf[10][1][8][1]
    assert timestamp[1][1] == (field.type.tz == "UTC")
    unit = {"ms": 1, "us": 2, "ns": 3}[field.type.unit]
    assert list(timestamp[2][1]) == [unit] and timestamp[2][1][unit][1] == {}
    expected_start = 4
    for index, values in enumerate(batches):
        group = parquet.metadata.row_group(index)
        chunk = group.column(0)
        physical = parquet.read_row_group(index).column(0).cast(pa.int64()).to_pylist()
        assert physical == values and group.num_rows == chunk.num_values == len(values)
        assert chunk.compression == "UNCOMPRESSED" and chunk.encodings == ("PLAIN", "RLE")
        start = chunk.data_page_offset
        assert start == expected_start and chunk.total_compressed_size > 0
        expected_start += chunk.total_compressed_size
        memory = TMemoryBuffer(wire[start:start + chunk.total_compressed_size])
        page = THRIFT["read_struct"](TCompactProtocol(memory))
        assert page[1][1] == 0 and page[2][1] == page[3][1]
        assert [page[5][1][key][1] for key in (1, 2, 3, 4)] == [len(values), 0, 3, 3]
        body = memory.readAll(page[3][1])
        if field.nullable:
            width, = struct.unpack_from("<I", body)
            assert body[4:4 + width] == bytes(x for value in values for x in (2, int(value is not None)))
            body = body[4 + width:]
        assert [value for value, in struct.iter_unpack("<q", body)] == [v for v in values if v is not None]
        assert memory.cstringio_buf.tell() == chunk.total_compressed_size
    footer_size, = struct.unpack_from("<I", wire, len(wire) - 8)
    assert expected_start == len(wire) - 8 - footer_size
    print(f"{field.type}: groups {list(map(len, batches))}, sha256={sha256(wire).hexdigest()}")


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    with tempfile.TemporaryDirectory(prefix="arrow-timestamp-to-parquet-") as temporary:
        directory = Path(temporary)
        fixtures = dict(cases())
        pin = sha256(b"".join(len(wire).to_bytes(8, "little") + wire for wire in fixtures.values())).hexdigest()
        print(f"IPC fixture-set SHA-256 {pin}", flush=True)
        assert pin == PIN
        for name, wire in fixtures.items():
            (directory / (name + ".arrows")).write_bytes(wire)
        emitter = ROOT / "scripts/arrow-timestamp-to-parquet-oracle/Emit.lean"
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(emitter), str(directory)], cwd=ROOT, check=True)
        outputs = sorted(directory.glob("*.parquet"))
        assert {file.stem for file in outputs} == {
            "ms_local", "ms_utc", "us_local", "us_utc", "ns_local", "ns_utc", "schema_only"}
        for output in outputs:
            verify(fixtures[output.stem], output.read_bytes())


if __name__ == "__main__":
    main()
