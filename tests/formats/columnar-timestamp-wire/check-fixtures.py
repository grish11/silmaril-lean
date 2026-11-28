"""Exercise Lean against actual timestamp value slices from PyArrow and parquet-java."""

import hashlib
from importlib.metadata import version
import json
import os
from pathlib import Path
from runpy import run_path
import struct
import subprocess
import tempfile

import pyarrow as pa
import pyarrow.ipc as ipc
import pyarrow.parquet as pq
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer


ROOT = Path(__file__).resolve().parents[3]
HEADER_FIELDS = run_path(str(ROOT / "scripts/parquet-scalar-page/PyArrowOracle.py"))["header_fields"]
ARROW_UNITS = {"s": "second", "ms": "millisecond", "us": "microsecond", "ns": "nanosecond"}
PARQUET_UNITS = {"ms": ("millis", "milliseconds"), "us": ("micros", "microseconds"),
                 "ns": ("nanos", "nanoseconds")}
TICKS = [-(2**63), -2001, -2, 0, 0x0102030405060708, 2**63 - 1]
PYARROW_FIXTURES_SHA256 = "6a6103c7ef51ea35e9c0aa5f51b81c9aaafbf0dd858c8031e6d4145e52ad9078"
JAVA_MANIFEST_SHA256 = "8fab794295cdfd337f6555f8dab12ab59416217087d16c48e196916239209db2"


def update_digest(digest, data):
    digest.update(len(data).to_bytes(8, "little"))
    digest.update(data)


def arrow_fixture(table, unit, timezone, digest):
    sink = pa.BufferOutputStream()
    options = ipc.IpcWriteOptions(metadata_version=ipc.MetadataVersion.V5)
    with ipc.new_stream(sink, table.schema, options=options) as writer:
        writer.write_table(table)
    ipc_bytes = sink.getvalue()
    array = ipc.open_stream(ipc_bytes).read_next_batch().column(0)
    assert (array.type.unit, array.type.tz) == (unit, timezone)
    assert array.offset == array.null_count == 0
    validity, values = array.buffers()
    assert validity is None
    payload = values.to_pybytes()
    assert len(payload) == 8 * len(TICKS)
    update_digest(digest, ipc_bytes)
    return payload


def parquet_fixture(table, unit, adjusted, digest):
    sink = pa.BufferOutputStream()
    pq.write_table(table, sink, version="2.6", data_page_version="1.0", compression="NONE",
                   use_dictionary=False, column_encoding="PLAIN", store_schema=False,
                   write_statistics=False, row_group_size=len(TICKS))
    data = sink.getvalue().to_pybytes()
    parquet = pq.ParquetFile(pa.BufferReader(data))
    assert parquet.metadata.num_row_groups == 1
    leaf = parquet.schema.column(0)
    assert leaf.max_definition_level == leaf.max_repetition_level == 0
    assert leaf.physical_type == "INT64"
    logical = json.loads(leaf.logical_type.to_json())
    assert (logical["Type"], logical["timeUnit"], logical["isAdjustedToUTC"]) == ("Timestamp", unit, adjusted)
    assert parquet.read().column(0).cast(pa.int64()).to_pylist() == TICKS
    column = parquet.metadata.row_group(0).column(0)
    assert column.compression == "UNCOMPRESSED" and not column.has_dictionary_page
    offset = column.data_page_offset
    size = column.total_compressed_size
    transport = TMemoryBuffer(data[offset:offset + size])
    header = HEADER_FIELDS(TCompactProtocol(transport), (5,))
    assert header[1] == 0 and header[5][2] == 0  # DATA_PAGE and PLAIN
    assert header[5][1] == len(TICKS)
    assert header[2] == header[3] == 8 * len(TICKS)
    assert transport.cstringio_buf.tell() + header[3] == size == column.total_uncompressed_size
    payload = transport.readAll(header[3])
    update_digest(digest, data)
    return payload


def add_checks(checks, metadata, decode, encode, kind, unit, payload, ticks):
    assert list(struct.unpack(f"<{len(ticks)}q", payload)) == ticks
    values = "[" + ", ".join(f"⟨{tick}⟩" for tick in ticks) + "]"
    checks.extend([
        f"#guard (match {metadata}.kind with | .{kind} => true | _ => false)",
        f"#guard ({metadata}.{decode} {len(ticks)} (Bytes.ofList {list(payload)})).toOption == "
        f"some ({values} : List (Ticks .{kind} .{unit}))",
        f"#guard ({metadata}.{encode} ({values} : List (Ticks .{kind} .{unit}))).toOption == "
        f"some (Bytes.ofList {list(payload)})",
    ])


def add_java_fixture(checks):
    manifest = (ROOT / "tests/formats/parquet-plain/parquet-java-1.16.0.tsv").read_bytes()
    assert hashlib.sha256(manifest).hexdigest() == JAVA_MANIFEST_SHA256
    row, = (line.decode().split("\t") for line in manifest.splitlines() if line.startswith(b"INT64\t"))
    _, count, hexadecimal = row
    ticks = [-(2**63), -2, 0, 0x0102030405060708, 2**63 - 1]
    assert int(count) == len(ticks)
    add_checks(checks, "(⟨.micros, false⟩ : Parquet.Metadata)", "decodePlain", "encodePlain",
               "localReading", "microsecond", bytes.fromhex(hexadecimal), ticks)


def main():
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    digest = hashlib.sha256()
    checks = []
    for unit, lean_unit in ARROW_UNITS.items():
        for timezone in (None, "Europe/Paris"):
            kind = "localReading" if timezone is None else "utcInstant"
            zone = "none" if timezone is None else f"some {json.dumps(timezone)}"
            schema = pa.schema([pa.field("time", pa.timestamp(unit, timezone), nullable=False)])
            array = pa.array(TICKS, type=pa.int64()).cast(schema.field(0).type)
            table = pa.Table.from_arrays([array], schema=schema)
            payload = arrow_fixture(table, unit, timezone, digest)
            metadata = f"(⟨.{lean_unit}, {zone}⟩ : Arrow.Metadata)"
            add_checks(checks, metadata, "decodeBufferLE", "encodeBufferLE", kind, lean_unit, payload, TICKS)
            if unit in PARQUET_UNITS:
                parquet_unit, file_unit = PARQUET_UNITS[unit]
                adjusted = timezone is not None
                payload = parquet_fixture(table, file_unit, adjusted, digest)
                metadata = f"(⟨.{parquet_unit}, {str(adjusted).lower()}⟩ : Parquet.Metadata)"
                add_checks(checks, metadata, "decodePlain", "encodePlain", kind, lean_unit, payload, TICKS)
    assert digest.hexdigest() == PYARROW_FIXTURES_SHA256, f"PyArrow fixture hash {digest.hexdigest()}"
    add_java_fixture(checks)

    imports = [
        "module",
        "import Silmaril.Formats.ColumnarTimestamp.Wire.Defs",
        "meta import Silmaril.Formats.ColumnarTimestamp.Wire.Defs",
        "meta import Silmaril.Formats.ColumnarTimestamp.Defs",
        "meta import Silmaril.Numeric.Timestamp.Defs",
        "meta import Silmaril.Formats.Bytes",
        "open Silmaril.Formats (Bytes)",
        "open Silmaril.Formats.ColumnarTimestamp Silmaril.Numeric.Timestamp",
    ]
    with tempfile.TemporaryDirectory() as temp:
        lean = Path(temp) / "Fixtures.lean"
        lean.write_text("\n".join(imports + checks) + "\n", encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(lean)], cwd=ROOT, check=True)
    print(f"{len(checks)} Lean fixture checks on eight Arrow buffers and six Parquet PLAIN values slices "
          "from PyArrow 26.0.1, and one parquet-java 1.16.0 INT64 PLAIN fixture")
    print(f"PyArrow fixture bytes SHA-256 {PYARROW_FIXTURES_SHA256}")
    print(f"parquet-java manifest SHA-256 {JAVA_MANIFEST_SHA256}")


if __name__ == "__main__":
    main()
