"""Check pinned INT96 producers and independently read IPC from the event adapter."""

import argparse
from copy import deepcopy
from hashlib import sha256
from importlib.metadata import version
import os
from pathlib import Path
import platform
import runpy
import struct
import subprocess
import tempfile

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "data/parquet-int96-arrow-events"
MIXED_DATA = ROOT / "data/parquet-int96-mixed-file"
DICTIONARY_DATA = ROOT / "data/parquet-int96-dictionary-file"
MIXED = runpy.run_path(str(ROOT / "scripts/parquet-int96-mixed-file/check-fixtures.py"))
THRIFT = MIXED["THRIFT"]
SHA256 = {
    "fallback-v1": "80dd266b7688d348f693f79156bcaf95e769067698cb8768c562d20ef7201e48",
    "fallback-v2": "d67ed9717daa33b5a315f630bf18d621abd1afeeb3cefd5c738ffa32ca25aa08",
    "required-v1": "54b61503be406fefaabc16ba7d4197ddb8fb1fa5dd43bd90c56b5549d3d57b0e",
    "v2-empty": "f8b1137da926c496eb3cca4b9e5988896ff1774d8a46f38418e3492c4c9188dd",
    "v2-precision": "efd6355f7f6be14c3496dc7e6634582fd60bf690a2694457fc3e7b0082d21338",
}


def empty_data(tag, payload=b""):
    header = {tag_slot: (TType.I32, 0) for tag_slot in (1, 2, 3, 5, 6)}
    header[4] = TType.I32, tag
    header[7] = TType.BOOL, False
    return THRIFT["encode"]({
        1: (TType.I32, 3), 2: (TType.I32, len(payload)), 3: (TType.I32, len(payload)),
        8: (TType.STRUCT, header),
    }) + payload


def with_empty_group(wire):
    """Add a zero-count framed group at footer ordinal 1 using Compact Thrift."""
    footer_size, = struct.unpack_from("<I", wire, len(wire) - 8)
    start = len(wire) - 8 - footer_size
    decoy = empty_data(0)
    dictionary = THRIFT["encode"]({
        1: (TType.I32, 2), 2: (TType.I32, 0), 3: (TType.I32, 0),
        7: (TType.STRUCT, {1: (TType.I32, 0), 2: (TType.I32, 0)}),
    })
    selected = dictionary + empty_data(8, b"\x00")

    def add_group(metadata):
        groups = THRIFT["list_field"](metadata, 4)
        entry = deepcopy(groups[0])
        for key, value in ((2, len(decoy) + len(selected)), (3, 0), (5, start),
                           (6, len(decoy) + len(selected))):
            entry[key] = entry[key][0], value
        groups.insert(1, entry)
        for index, (payload, offset) in enumerate(((decoy, start), (selected, start + len(decoy)))):
            column = THRIFT["column_metadata"](metadata, 1, index)
            page_offset = offset if index == 0 else offset + len(dictionary)
            for key, value in ((5, 0), (6, len(payload)), (7, len(payload)), (9, page_offset)):
                column[key] = column[key][0], value
            if index == 1:
                column[11] = column[11][0], offset
            for key in (12, 13, 16):
                column.pop(key, None)

    return THRIFT["rewrite_footer"](wire[:start] + decoy + selected + wire[start:], add_group)


def with_late_precision(wire):
    # In group 1 the second present PLAIN word is logical slot 10.
    offset = 750
    subday, julian = struct.unpack_from("<Qi", wire, offset)
    assert (subday, julian) == MIXED["CHUNK"]["words"]([(10**16 - 102) * 1000])[0]
    assert subday + 1 < MIXED["CHUNK"]["DAY_NS"]
    return wire[:offset] + struct.pack("<Q", subday + 1) + wire[offset + 8:]


def assert_pin(name, wire):
    digest = sha256(wire).hexdigest()
    assert digest == SHA256[name], f"unexpected {name} SHA-256"
    print(f"{digest}  {name}")


def read_grouped(wire, unit):
    source = pq.ParquetFile(pa.BufferReader(wire), coerce_int96_timestamp_unit=unit)
    batches = [source.read_row_group(index, columns=["legacy_ts"], use_threads=False).
               column(0).cast(pa.int64()).to_pylist() for index in range(source.metadata.num_row_groups)]
    return source, batches


def fixtures(write):
    v1 = (MIXED_DATA / "fallback-v1.parquet").read_bytes()
    v2 = (MIXED_DATA / "fallback-v2.parquet").read_bytes()
    endpoints = (DICTIONARY_DATA / "required-v1.parquet").read_bytes()
    for name, wire in (("fallback-v1", v1), ("fallback-v2", v2), ("required-v1", endpoints)):
        assert_pin(name, wire)
    empty = with_empty_group(v2)
    late_precision = with_late_precision(v2)
    for name, wire in (("v2-empty", empty), ("v2-precision", late_precision)):
        assert_pin(name, wire)
        path = DATA / (name + ".parquet")
        if write:
            path.write_bytes(wire)
        assert path.read_bytes() == wire
    _, baseline = read_grouped(v2, "us")
    empty_file, values = read_grouped(empty, "us")
    assert values == [baseline[0], [], baseline[1], baseline[2]]
    column = empty_file.metadata.row_group(1).column(1)
    assert column.num_values == 0 and column.dictionary_page_offset < column.data_page_offset
    start = column.dictionary_page_offset
    memory = TMemoryBuffer(empty[start:start + column.total_compressed_size])
    protocol = TCompactProtocol(memory)
    dictionary, _, body = MIXED["CHUNK"]["frame"](protocol, start)
    assert dictionary[1][1] == 2 and [dictionary[7][1][key][1] for key in (1, 2)] == [0, 0]
    assert body == b"" and start + memory.cstringio_buf.tell() == column.data_page_offset
    data, _, body = MIXED["CHUNK"]["frame"](protocol, start)
    assert data[1][1] == 3 and [data[8][1][key][1] for key in (1, 2, 3, 4, 5, 6)] == [0, 0, 0, 8, 0, 0]
    assert body == b"\x00" and memory.cstringio_buf.tell() == column.total_compressed_size
    _, endpoint_groups = read_grouped(endpoints, "ns")
    assert endpoint_groups[0][0] == -(2**63) and endpoint_groups[0][2] == 2**63 - 1
    return [(MIXED_DATA / "fallback-v1.parquet", "ns", True),
            (DATA / "v2-empty.parquet", "us", True),
            (DICTIONARY_DATA / "required-v1.parquet", "ns", False)]


def check_readback(source, unit, nullable, timezone, directory):
    _, expected = read_grouped(source.read_bytes(), unit)
    schema = pa.schema([pa.field("legacy_ts", pa.timestamp(unit, timezone), nullable=nullable)])
    sink = pa.BufferOutputStream()
    with pa.ipc.new_stream(sink, schema):
        pass
    schema_stream = sink.getvalue().to_pybytes()
    eos = bytes([0xFF, 0xFF, 0xFF, 0xFF, 0, 0, 0, 0])
    assert schema_stream.endswith(eos)
    schema_file = directory / "schema"
    output = directory / "stream"
    schema_file.write_bytes(schema_stream[:-8])
    subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DwarningAsError=true",
                    "--run", str(ROOT / "scripts/parquet-int96-arrow-events/Emit.lean"),
                    str(source), str(schema_file), str(output), unit,
                    "utc" if timezone else "local", "optional" if nullable else "required"],
                   cwd=ROOT, check=True)
    observed = output.read_bytes()
    assert observed.endswith(eos)
    with pa.ipc.open_stream(observed) as stream:
        assert stream.schema.equals(schema, check_metadata=True)
        assert [batch.column(0).cast(pa.int64()).to_pylist() for batch in stream] == expected
    print(f"PyArrow IPC readback {source.name} {unit} {timezone or 'local'}: batch sizes {list(map(len, expected))}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--fixtures-only", action="store_true")
    args = parser.parse_args()
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    cases = fixtures(args.write)
    if not args.fixtures_only:
        with tempfile.TemporaryDirectory(prefix="int96-arrow-events-") as temporary:
            for source, unit, nullable in cases:
                for timezone in (None, "UTC"):
                    check_readback(source, unit, nullable, timezone, Path(temporary))


if __name__ == "__main__":
    main()
