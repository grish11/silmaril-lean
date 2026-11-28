"""Check timestamp descriptors and PLAIN bytes from a pinned PyArrow file."""

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
import pyarrow.parquet as pq
from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer


ROOT = Path(__file__).resolve().parents[3]
HEADER_FIELDS = run_path(str(ROOT / "scripts/parquet-scalar-page/PyArrowOracle.py"))["header_fields"]
FIXTURE_SHA256 = "ae216b4bdfc6f3c8a82a26cb11af42458c7af802862887e249ec7d81a787921d"
TICKS = [-(2**63), -2001, -1, 0, 0x0102030405060708, 2**63 - 1]
UNITS = {"ms": ("millis", "milliseconds", "TIMESTAMP_MILLIS"),
         "us": ("micros", "microseconds", "TIMESTAMP_MICROS"),
         "ns": ("nanos", "nanoseconds", "NONE")}


def plain_body(data, column, count):
    assert not column.has_dictionary_page and column.compression == "UNCOMPRESSED"
    offset, size = column.data_page_offset, column.total_compressed_size
    transport = TMemoryBuffer(data[offset:offset + size])
    page = HEADER_FIELDS(TCompactProtocol(transport), (5,))
    assert page[1] == 0 and page[5][2] == 0  # DATA_PAGE, PLAIN
    assert page[5][1] == count
    assert page[2] == page[3] == 8 * count
    assert transport.cstringio_buf.tell() + page[3] == size == column.total_uncompressed_size
    return transport.readAll(page[3])


def add_writer_fixture(lines, directory):
    fields = [pa.field("decoy_i32", pa.int32(), nullable=False)]
    arrays = [pa.array([7] * len(TICKS), type=pa.int32())]
    columns = []
    for unit in UNITS:
        for adjusted in (False, True):
            name = unit + ("_utc" if adjusted else "_local")
            type_ = pa.timestamp(unit, "UTC" if adjusted else None)
            fields.append(pa.field(name, type_, nullable=False))
            # Make adjacent columns' values differ as well as their annotations.
            ticks = TICKS if adjusted else list(reversed(TICKS))
            arrays.append(pa.array(ticks, type=pa.int64()).cast(type_))
            columns.append((name, unit, adjusted, ticks))
    fields.append(pa.field("plain_i64", pa.int64(), nullable=False))
    arrays.append(pa.array(TICKS, type=pa.int64()))
    table = pa.Table.from_arrays(arrays, schema=pa.schema(fields))
    sink = pa.BufferOutputStream()
    pq.write_table(table, sink, version="2.6", data_page_version="1.0", compression="NONE",
                   use_dictionary=False, column_encoding="PLAIN", store_schema=False,
                   write_statistics=False, row_group_size=len(TICKS))
    data = sink.getvalue().to_pybytes()
    digest = hashlib.sha256(data).hexdigest()
    assert digest == FIXTURE_SHA256, f"PyArrow Parquet fixture SHA-256 {digest}"
    path = directory / "annotated.parquet"
    path.write_bytes(data)
    parquet = pq.ParquetFile(pa.BufferReader(data))
    assert parquet.metadata.num_row_groups == 1
    decoded = parquet.read()
    lines.extend([
        "private def checkWriter : IO Unit := do",
        f"  let file : Bytes := ⟨← IO.FS.readBinFile {json.dumps(str(path))}⟩",
        '  expectError file 0 .notInt64Leaf',
        '  expectError file 1 .notInt64Leaf',
        '  expectError file 8 (.missingField 10)',
        '  expectError file 9 (.schemaIndex 9)',
    ])
    for index, (name, unit, adjusted, ticks) in enumerate(columns, 1):
        lean_unit, parquet_unit, converted = UNITS[unit]
        leaf = parquet.schema.column(index)
        logical = json.loads(leaf.logical_type.to_json())
        assert (leaf.name, leaf.max_definition_level, leaf.max_repetition_level) == (name, 0, 0)
        assert leaf.physical_type == "INT64" and leaf.converted_type == (converted if adjusted else "NONE")
        assert (logical["Type"], logical["timeUnit"], logical["isAdjustedToUTC"]) == (
            "Timestamp", parquet_unit, adjusted)
        assert decoded[name].cast(pa.int64()).to_pylist() == ticks
        payload = plain_body(data, parquet.metadata.row_group(0).column(index), len(ticks))
        assert list(struct.unpack(f"<{len(ticks)}q", payload)) == ticks
        lines.append(f'  let binding ← checkBinding file {index + 1} "{name}" .{lean_unit} '
                     f'{str(adjusted).lower()}')
        lines.append(f"  checkPayload binding {list(payload)} {ticks}")
    return len(columns)


def write_fields(protocol, fields):
    protocol.writeStructBegin("")
    for field, tag, value in fields:
        protocol.writeFieldBegin("", tag, field)
        if tag == TType.STRUCT:
            write_fields(protocol, value)
        elif tag == TType.LIST:
            protocol.writeListBegin(TType.STRUCT, len(value))
            for item in value:
                write_fields(protocol, item)
            protocol.writeListEnd()
        else:
            write = {TType.I32: protocol.writeI32, TType.I64: protocol.writeI64,
                     TType.BOOL: protocol.writeBool, TType.STRING: protocol.writeString}[tag]
            write(value)
        protocol.writeFieldEnd()
    protocol.writeFieldStop()
    protocol.writeStructEnd()


def modern(fields):
    return (10, TType.STRUCT, [(8, TType.STRUCT, fields)])


def unit_field(*arms):
    return (2, TType.STRUCT, [(arm, TType.STRUCT, []) for arm in arms])


def synthetic(annotations, physical=2, extra=(), trailing=b""):
    root = [(4, TType.STRING, "schema"), (5, TType.I32, 1)]
    leaf = [(1, TType.I32, physical), (3, TType.I32, 0), (4, TType.STRING, "time")]
    transport = TMemoryBuffer()
    write_fields(TCompactProtocol(transport), [
        (1, TType.I32, 2), (2, TType.LIST, [root, leaf + list(extra) + annotations]),
        (3, TType.I64, 0), (4, TType.LIST, []),
    ])
    footer = transport.getvalue() + trailing
    return b"PAR1" + footer + struct.pack("<I", len(footer)) + b"PAR1"


def add_structural_fixtures(lines, directory):
    flag = (1, TType.BOOL, False)
    legacy_ms, legacy_us = (6, TType.I32, 9), (6, TType.I32, 10)
    millis = modern([flag, unit_field(1)])
    nanos = modern([flag, unit_field(3)])
    cases = [
        ([legacy_ms], '(.missingField 10)'),
        ([millis, millis], '(.duplicateField 10)'),
        ([legacy_ms, legacy_ms, millis], '(.duplicateField 6)'),
        ([legacy_us, millis], '(.convertedType 10)'),
        ([legacy_ms, nanos], '(.convertedType 9)'),
        ([(6, TType.BOOL, True), millis], '(.fieldType 6)'),
        ([(10, TType.I32, 8)], '(.fieldType 10)'),
        ([(10, TType.STRUCT, [(7, TType.STRUCT, [])])], '.logicalUnion'),
        ([(10, TType.STRUCT, millis[2] + [(7, TType.STRUCT, [])])], '.logicalUnion'),
        ([modern([unit_field(1)])], '(.missingField 1)'),
        ([modern([flag, flag, unit_field(1)])], '(.duplicateField 1)'),
        ([modern([(1, TType.I32, 0), unit_field(1)])], '(.fieldType 1)'),
        ([modern([flag])], '(.missingField 2)'),
        ([modern([flag, unit_field(1), (3, TType.I32, 0)])], '.timestampFields'),
        ([modern([flag, unit_field()])], '.unitUnion'),
        ([modern([flag, unit_field(1, 2)])], '.unitUnion'),
        ([modern([flag, unit_field(4)])], '.unitUnion'),
        ([modern([flag, (2, TType.STRUCT, [(1, TType.STRUCT, [(1, TType.I32, 0)])])])], '.unitUnion'),
    ]
    bodies = [(synthetic(annotations), error) for annotations, error in cases]
    bodies.extend([
        (synthetic([millis], physical=1), '.notInt64Leaf'),
        (synthetic([millis], extra=[(5, TType.I32, 1)]), '.notInt64Leaf'),
        (synthetic([millis], trailing=b"\0"), '(.footer .trailingMetadata)'),
        (synthetic([millis])[:-1], '(.footer (.framing .trailingMagic))'),
    ])
    lines.append("private def checkStructural : IO Unit := do")
    for index, (data, error) in enumerate(bodies):
        path = directory / f"malformed-{index}.parquet"
        path.write_bytes(data)
        lines.append(f"  expectError ⟨← IO.FS.readBinFile {json.dumps(str(path))}⟩ 1 {error}")
    path = directory / "reordered-fields.parquet"
    path.write_bytes(synthetic([modern([unit_field(1), flag]), legacy_ms]))
    lines.append(f"  let file : Bytes := ⟨← IO.FS.readBinFile {json.dumps(str(path))}⟩")
    lines.append('  let _ ← checkBinding file 1 "time" .millis false')
    lines.append('  pure ()')
    return len(bodies)


HARNESS = '''module
import Silmaril.Formats.Parquet.Timestamp.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Defs
meta import Silmaril.Formats.Parquet.Footer.Defs
meta import Silmaril.Formats.ColumnarTimestamp.Wire.Defs
meta import Silmaril.Formats.ColumnarTimestamp.Defs
meta import Silmaril.Numeric.Timestamp.Defs
meta import Silmaril.Formats.Bytes
open Silmaril.Formats Silmaril.Formats.Parquet.Timestamp Silmaril.Numeric.Timestamp
private def check (test : Bool) (label : String) : IO Unit :=
  unless test do throw (IO.userError label)
private def expectError (file : Bytes) (index : Nat) (reason : Error) : IO Unit :=
  match readFooter {} index file with
  | .error actual => check (actual == reason) s!"expected {repr reason}, got {repr actual}"
  | .ok _ => throw (IO.userError s!"accepted malformed fixture for {repr reason}")
private def checkBinding (file : Bytes) (index : Nat) (name : String)
    (unit : ColumnarTimestamp.Parquet.TimeUnit) (adjusted : Bool) : IO Binding := do
  let binding ← match readFooter {} index file with
    | .ok binding => pure binding
    | .error reason => throw (IO.userError s!"{name}: {repr reason}")
  check (binding.leaf.name == name && binding.descriptor.unit == unit &&
    binding.descriptor.isAdjustedToUTC == adjusted) s!"descriptor at {index}"
  pure binding
private def checkPayload (binding : Binding) (octets : List UInt8) (expected : List Int) : IO Unit := do
  let bytes := Bytes.ofList octets
  let ticks ← match binding.decodePlain expected.length bytes with
    | .ok ticks => pure ticks
    | .error reason => throw (IO.userError s!"payload: {repr reason}")
  check (ticks.map Ticks.ticks == expected) "ordered ticks"
  check ((binding.descriptor.encodePlain ticks).toOption == some bytes) "byte round trip"
'''


def main():
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    with tempfile.TemporaryDirectory() as temporary:
        directory = Path(temporary)
        lines = [HARNESS]
        columns = add_writer_fixture(lines, directory)
        malformed = add_structural_fixtures(lines, directory)
        lean = directory / "Fixture.lean"
        lean.write_text("\n".join(lines + ["#eval checkWriter", "#eval checkStructural"]) + "\n")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(lean)], cwd=ROOT, check=True)
    print(f"PyArrow 26.0.1: {columns} ordered timestamp leaves and their exact PLAIN bytes passed")
    print(f"PyArrow Parquet fixture SHA-256 {FIXTURE_SHA256}")
    print(f"Apache Thrift 0.25.0: {malformed} malformed footers and one reordered valid footer passed")


if __name__ == "__main__":
    main()
