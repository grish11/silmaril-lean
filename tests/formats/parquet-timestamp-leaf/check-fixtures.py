"""Check selected TIMESTAMP leaves against pinned PyArrow files and Thrift edits."""

import hashlib
from importlib.metadata import version
import json
import os
from pathlib import Path
import platform
import struct
import subprocess
import tempfile

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer


ROOT = Path(__file__).resolve().parents[3]
FIXTURE_SHA256 = "5589aa865a58d767d04d6bc992917930691ff655c073a21cb18ef661f86db702"
UNITS = {"ms": ("millis", "milliseconds"), "us": ("micros", "microseconds"),
         "ns": ("nanos", "nanoseconds")}
GROUP_SIZE = 6
MIN, MAX = -(2**63), 2**63 - 1
SCALAR = {TType.BOOL: "Bool", TType.I32: "I32", TType.I64: "I64",
           TType.STRING: "Binary", TType.BYTE: "Byte", TType.I16: "I16",
           TType.DOUBLE: "Double"}


def read_struct(protocol):
    fields = {}
    protocol.readStructBegin()
    while True:
        _, kind, index = protocol.readFieldBegin()
        if kind == TType.STOP:
            break
        assert index not in fields
        fields[index] = kind, read_value(protocol, kind)
        protocol.readFieldEnd()
    protocol.readStructEnd()
    return fields


def read_value(protocol, kind):
    if kind == TType.STRUCT:
        return read_struct(protocol)
    if kind == TType.LIST:
        item, count = protocol.readListBegin()
        values = [read_value(protocol, item) for _ in range(count)]
        protocol.readListEnd()
        return item, values
    return getattr(protocol, "read" + SCALAR[kind])()


def write_struct(protocol, fields):
    protocol.writeStructBegin("")
    for index, (kind, value) in sorted(fields.items()):
        protocol.writeFieldBegin("", kind, index)
        write_value(protocol, kind, value)
        protocol.writeFieldEnd()
    protocol.writeFieldStop()
    protocol.writeStructEnd()


def write_value(protocol, kind, value):
    if kind == TType.STRUCT:
        write_struct(protocol, value)
    elif kind == TType.LIST:
        item, values = value
        protocol.writeListBegin(item, len(values))
        for element in values:
            write_value(protocol, item, element)
        protocol.writeListEnd()
    else:
        getattr(protocol, "write" + SCALAR[kind])(value)


def encode(fields):
    memory = TMemoryBuffer()
    write_struct(TCompactProtocol(memory), fields)
    return memory.getvalue()


def rewrite_footer(wire, change):
    size, = struct.unpack_from("<I", wire, len(wire) - 8)
    start = len(wire) - 8 - size
    memory = TMemoryBuffer(wire[start:-8])
    metadata = read_struct(TCompactProtocol(memory))
    assert memory.cstringio_buf.tell() == size
    change(metadata)
    tail = encode(metadata)
    return wire[:start] + tail + struct.pack("<I", len(tail)) + b"PAR1"


def list_field(fields, index):
    return fields[index][1][1]


def column_metadata(metadata, group=0, column=1):
    return list_field(list_field(metadata, 4)[group], 1)[column][3][1]


def producer(page_version, *, crc=False, dictionary=False, compression="NONE"):
    fields = [pa.field("decoy_i32", pa.int32(), nullable=False)]
    arrays = [pa.array(range(12), type=pa.int32())]
    expected = []
    for unit in UNITS:
        for adjusted in (False, True):
            name = unit + ("_utc" if adjusted else "_local")
            number = len(expected) + 1
            nullable = not (unit == "ns" and adjusted)
            ticks = [MIN, -2001 * number, None if nullable else -1, 0, number, MAX,
                     -number, -1, MAX, None if nullable else 0, number * 1009, MIN]
            timestamp = pa.timestamp(unit, "UTC" if adjusted else None)
            fields.append(pa.field(name, timestamp, nullable=nullable))
            arrays.append(pa.array(ticks, type=pa.int64()).view(timestamp))
            expected.append((name, unit, adjusted, nullable, ticks))
    fields.append(pa.field("plain_i64", pa.int64(), nullable=False))
    arrays.append(pa.array(range(12), type=pa.int64()))
    sink = pa.BufferOutputStream()
    options = {} if dictionary else {"column_encoding": "PLAIN"}
    pq.write_table(pa.Table.from_arrays(arrays, schema=pa.schema(fields)), sink,
                   version="2.6", data_page_version=page_version, compression=compression,
                   use_dictionary=dictionary, write_statistics=False, write_page_checksum=crc,
                   store_schema=False, row_group_size=GROUP_SIZE, write_batch_size=2,
                   data_page_size=16, **options)
    return sink.getvalue().to_pybytes(), expected


def check_pages(wire, column, page_type):
    start = column.data_page_offset
    stop = start + column.total_compressed_size
    memory = TMemoryBuffer(wire[start:stop])
    protocol = TCompactProtocol(memory)
    count = 0
    while memory.cstringio_buf.tell() < stop - start:
        info = read_struct(protocol)
        assert info[1][1] == page_type
        memory.readAll(info[3][1])
        count += 1
    assert memory.cstringio_buf.tell() == stop - start and count >= 2


def rewrite_v1_encoding(wire):
    parquet = pq.ParquetFile(pa.BufferReader(wire))
    offset = parquet.metadata.row_group(0).column(1).data_page_offset
    memory = TMemoryBuffer(wire[offset:])
    page = read_struct(TCompactProtocol(memory))
    size = memory.cstringio_buf.tell()
    data = page[5][1]
    assert data[2] == (TType.I32, 0)
    data[2] = TType.I32, 5
    replacement = encode(page)
    assert len(replacement) == size
    return wire[:offset] + replacement + wire[offset + size:]


def lean_ticks(values):
    return "[" + ", ".join("none" if value is None else f"some ({value})" for value in values) + "]"


def observed(wire, ordinal, expected, page_type):
    parquet = pq.ParquetFile(pa.BufferReader(wire))
    name, unit, adjusted, nullable, ticks = expected
    leaf = parquet.schema.column(ordinal - 1)
    logical = json.loads(leaf.logical_type.to_json())
    assert (leaf.name, leaf.physical_type, leaf.max_definition_level, leaf.max_repetition_level) == (
        name, "INT64", int(nullable), 0)
    assert (logical["Type"], logical["timeUnit"], logical["isAdjustedToUTC"]) == (
        "Timestamp", UNITS[unit][1], adjusted)
    assert parquet.metadata.num_row_groups == 2
    groups = []
    for group in range(2):
        column = parquet.metadata.row_group(group).column(ordinal - 1)
        check_pages(wire, column, page_type)
        raw = parquet.read_row_group(group, columns=[name], use_threads=False).column(0).cast(pa.int64())
        values = raw.to_pylist()
        assert values == ticks[group * GROUP_SIZE:(group + 1) * GROUP_SIZE]
        groups.append(lean_ticks(values))
    return f'{ordinal} "{name}" .{UNITS[unit][0]} {str(adjusted).lower()} {str(nullable).lower()} ' + (
        "[" + ", ".join(groups) + "]")


def fixtures(directory):
    base, expected = producer("1.0")
    v2, _ = producer("2.0")
    files = {"v1": base, "v2": v2}
    lines = ["private def fixtures : IO Unit := do"]

    def file(name):
        return f"⟨← IO.FS.readBinFile {json.dumps(str(directory / (name + '.parquet')))}⟩"

    for name, page_type in (("v1", 0), ("v2", 3)):
        for ordinal, field in enumerate(expected, 2):
            lines.append(f"  checkGroups {file(name)} {observed(files[name], ordinal, field, page_type)}")

    def annotation(metadata, ordinal, converted, modern=True):
        leaf = list_field(metadata, 2)[ordinal]
        leaf[6] = TType.I32, converted
        if not modern:
            del leaf[10]

    files["local_with_matching_tag"] = rewrite_footer(base, lambda m: annotation(m, 2, 9))
    name = "local_with_matching_tag"
    lines.append(f"  checkGroups {file(name)} {observed(files[name], 2, expected[0], 0)}")
    files["local_with_conflicting_tag"] = rewrite_footer(base, lambda m: annotation(m, 2, 10))
    files["nanos_with_tag"] = rewrite_footer(base, lambda m: annotation(m, 6, 9))
    files["legacy_only"] = rewrite_footer(base, lambda m: annotation(m, 2, 9, modern=False))
    def wrong_path(metadata):
        column_metadata(metadata)[3] = TType.LIST, (TType.STRING, [b"us_utc"])

    files["bad_path"] = rewrite_footer(base, wrong_path)
    files["truncated_file"] = base[:-1]
    for name, ordinal, reason in (
        ("v1", 0, ".annotation .notInt64Leaf"),
        ("v1", 1, ".annotation .notInt64Leaf"),
        ("v1", 8, ".annotation (.missingField 10)"),
        ("v1", 9, ".annotation (.schemaIndex 9)"),
        ("local_with_conflicting_tag", 2, ".annotation (.convertedType 10)"),
        ("nanos_with_tag", 6, ".annotation (.convertedType 9)"),
        ("legacy_only", 2, ".annotation (.missingField 10)"),
        ("bad_path", 2, ".snapshot (.invalidMetadata .columns)"),
        ("truncated_file", 2, ".snapshot (.footer (.framing .trailingMagic))"),
    ):
        lines.append(f"  expectError (openLeaf {{}} {file(name)} {ordinal}) ({reason})")

    def alias(metadata):
        selected = column_metadata(metadata)
        other = column_metadata(metadata, group=1, column=2)
        selected[7], selected[9] = other[7], other[9]

    def wrong_page_total(metadata):
        metadata[3] = TType.I64, 2 * GROUP_SIZE + 1
        list_field(metadata, 4)[0][3] = TType.I64, GROUP_SIZE + 1
        column_metadata(metadata)[5] = TType.I64, GROUP_SIZE + 1

    def wrong_chunk_count(metadata):
        column_metadata(metadata)[5] = TType.I64, GROUP_SIZE - 1

    def cut_page(metadata):
        column = column_metadata(metadata)
        column[7] = TType.I64, column[7][1] - 1

    files["aliased_chunk"] = rewrite_footer(base, alias)
    files["wrong_chunk_count"] = rewrite_footer(base, wrong_chunk_count)
    files["wrong_page_total"] = rewrite_footer(base, wrong_page_total)
    files["truncated_chunk"] = rewrite_footer(base, cut_page)
    files["wrong_page_encoding"] = rewrite_v1_encoding(base)
    files["crc"] = producer("1.0", crc=True)[0]
    files["dictionary"] = producer("1.0", dictionary=True)[0]
    files["compressed"] = producer("2.0", compression="SNAPPY")[0]
    for name, group, limits, reason in (
        ("v1", 2, "{}", ".groupIndex 2"),
        ("v1", 0, "{ maxRows := 5 }", ".rowLimit"),
        ("v1", 0, "{ page := { ({} : Limits).page with compressedBytes := 0 } }",
         ".page 0 (.scalar (.payload .compressedLimit))"),
        ("aliased_chunk", 0, "{}", ".chunkOverlap"),
        ("wrong_chunk_count", 0, "{}", ".chunkCount 6 5"),
        ("wrong_page_total", 0, "{}", ".rowCount 7 6"),
        ("truncated_chunk", 0, "{}", ".framing .payloadBounds"),
        ("wrong_page_encoding", 0, "{}", ".page 0 (.scalar (.unsupportedEncoding 5))"),
        ("crc", 0, "{}", ".crcUnsupported 0"),
        ("dictionary", 0, "{}", ".chunkEncoding"),
        ("compressed", 0, "{}", ".chunkCodec 1"),
    ):
        lines.append(f"  let bound ← require (openLeaf {{}} {file(name)} 2)")
        lines.append(f"  expectError (readGroup {limits} bound {group}) ({reason})")
    return files, lines


LEAN = """module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Defs
meta import Silmaril.Formats.ColumnarTimestamp.Defs
meta import Silmaril.Numeric.Timestamp.Defs

open Silmaril.Formats Silmaril.Formats.Parquet.Timestamp.Leaf Silmaril.Numeric.Timestamp

private def check (test : Bool) (label : String) : IO Unit :=
  unless test do throw (IO.userError label)

private def require {α : Type} (result : Except Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error reason => throw (IO.userError s!"{repr reason}")

private def expectError {α : Type} (result : Except Error α) (reason : Error) : IO Unit :=
  match result with
  | .error actual => check (actual == reason) s!"expected {repr reason}, received {repr actual}"
  | .ok _ => throw (IO.userError s!"expected {repr reason}, received success")

private def checkGroups (wire : Bytes) (ordinal : Nat) (name : String)
    (unit : ColumnarTimestamp.Parquet.TimeUnit) (adjusted nullable : Bool)
    (expected : List (List (Option Int))) : IO Unit := do
  let bound ← require (openLeaf {} wire ordinal)
  let descriptor := bound.binding.descriptor
  check (bound.ordinal == ordinal && bound.binding.leaf.name == name &&
    descriptor.unit == unit && descriptor.isAdjustedToUTC == adjusted &&
    bound.binding.leaf.repetition == some (if nullable then .optional else .required)) "bound leaf"
  for (ticks, index) in expected.zipIdx do
    let slots ← require (readGroup {} bound index)
    check (slots.map (Option.map Ticks.ticks) == ticks) s!"slots for {name} group {index}"
"""


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    with tempfile.TemporaryDirectory() as temporary:
        directory = Path(temporary)
        files, lines = fixtures(directory)
        digest = hashlib.sha256()
        for name, data in sorted(files.items()):
            digest.update(len(data).to_bytes(8, "little"))
            digest.update(data)
            (directory / (name + ".parquet")).write_bytes(data)
        assert digest.hexdigest() == FIXTURE_SHA256, f"fixture SHA-256 {digest.hexdigest()}"
        driver = directory / "Fixture.lean"
        driver.write_text("\n".join([LEAN, *lines, "#eval fixtures"]) + "\n", encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(driver)], cwd=ROOT, check=True)
    print("PyArrow 26.0.1 and Thrift 0.25.0: 26 selected groups and 20 typed failures passed")
    print(f"Length-framed fixture SHA-256 {FIXTURE_SHA256}")


if __name__ == "__main__":
    main()
