"""Check the Parquet DATE binder against pinned PyArrow files and Thrift edits."""

import argparse
from datetime import date, timedelta
import hashlib
import json
import os
from pathlib import Path
import platform
import struct
import subprocess
import sys
import tempfile

from importlib.metadata import version

MANIFEST = Path(__file__).resolve().with_name("fixtures.json")
REPO = MANIFEST.parents[2]
EDGE_DAYS = [-(2**31), -719528, -1, None, 0, 11016, 2**31 - 1]


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def fields(protocol):
    protocol.readStructBegin()
    while True:
        _, kind, field = protocol.readFieldBegin()
        if kind == TType.STOP:
            break
        yield kind, field
        protocol.readFieldEnd()
    protocol.readStructEnd()


def leaf_annotation(protocol):
    info = {}
    for kind, field in fields(protocol):
        if field in (1, 3, 6):
            require(kind == TType.I32, f"Expected i32 field {field}")
            info[str(field)] = protocol.readI32()
        elif field == 4:
            require(kind == TType.STRING, "Expected schema name")
            info["4"] = protocol.readString()
        elif field == 10:
            require(kind == TType.STRUCT, "Expected LogicalType union")
            values = []
            for member_kind, member in fields(protocol):
                require(member_kind == TType.STRUCT, "Expected logical member struct")
                payload = []
                for child_kind, child in fields(protocol):
                    protocol.skip(child_kind)
                    payload.append(child)
                values.append([member, payload])
            info["10"] = values
        else:
            protocol.skip(kind)
    return info


def raw_leaf(wire):
    footer_start = len(wire) - 8 - struct.unpack_from("<I", wire, len(wire) - 8)[0]
    memory = TMemoryBuffer(wire[footer_start:-8])
    protocol = TCompactProtocol(memory)
    result = None
    for kind, field in fields(protocol):
        if field != 2:
            protocol.skip(kind)
            continue
        require(kind == TType.LIST, "Expected schema list")
        element_type, size = protocol.readListBegin()
        require((element_type, size) == (TType.STRUCT, 2), "Expected root plus one leaf")
        protocol.skip(element_type)
        start = memory.cstringio_buf.tell()
        info = leaf_annotation(protocol)
        stop = memory.cstringio_buf.tell()
        protocol.readListEnd()
        result = info, footer_start, start, stop
    require(result is not None, "Missing schema")
    require(memory.cstringio_buf.tell() == len(wire) - 8 - footer_start, "Trailing footer bytes")
    return result


def with_annotations(wire, converted, logical, leaf_name="date"):
    info, footer, start, stop = raw_leaf(wire)
    memory = TMemoryBuffer()
    protocol = TCompactProtocol(memory)
    protocol.writeStructBegin("SchemaElement")
    for index in (1, 3, 4, 6, 10):
        if (index == 6 and converted is None) or (index == 10 and logical is None):
            continue
        kind = {4: TType.STRING, 10: TType.STRUCT}.get(index, TType.I32)
        protocol.writeFieldBegin("", kind, index)
        if index in (1, 3):
            protocol.writeI32(info[str(index)])
        elif index == 4:
            protocol.writeString(leaf_name)
        elif index == 6:
            protocol.writeI32(converted)
        else:
            protocol.writeStructBegin("LogicalType")
            for member in logical:
                member_id, nonempty = (member, False) if isinstance(member, int) else member
                protocol.writeFieldBegin("", TType.STRUCT, member_id)
                protocol.writeStructBegin("DateType")
                if nonempty:
                    protocol.writeFieldBegin("", TType.I32, 1)
                    protocol.writeI32(0)
                    protocol.writeFieldEnd()
                protocol.writeFieldStop()
                protocol.writeStructEnd()
                protocol.writeFieldEnd()
            protocol.writeFieldStop()
            protocol.writeStructEnd()
        protocol.writeFieldEnd()
    protocol.writeFieldStop()
    protocol.writeStructEnd()
    new_footer = wire[footer:footer + start] + memory.getvalue() + wire[footer + stop:-8]
    return wire[:footer] + new_footer + struct.pack("<I", len(new_footer)) + b"PAR1"


def producer(values, arrow_type, nullable, page_version="1.0", crc=False, group_size=None):
    if arrow_type == pa.date32():
        column = pa.array(values, type=pa.int32()).view(arrow_type)
    else:
        column = pa.array(values, type=arrow_type)
    schema = pa.schema([pa.field("date", arrow_type, nullable=nullable)])
    sink = pa.BufferOutputStream()
    pq.write_table(pa.Table.from_arrays([column], schema=schema), sink,
                   version="2.6", data_page_version=page_version, compression="NONE",
                   use_dictionary=False, write_statistics=False, write_page_checksum=crc,
                   store_schema=False, row_group_size=group_size or len(values))
    return sink.getvalue().to_pybytes()


def host_observation(name, wire, expected, arrow_type, group):
    parquet = pq.ParquetFile(pa.BufferReader(wire))
    column = parquet.schema.column(0)
    require(column.physical_type == "INT32", f"{name}: physical type")
    chunk = parquet.metadata.row_group(group).column(0)
    require(chunk.compression == "UNCOMPRESSED" and not chunk.has_dictionary_page,
            f"{name}: physical profile")
    observed = parquet.read_row_group(group, use_threads=False).column(0).combine_chunks()
    require(observed.type == arrow_type and observed.view(pa.int32()).to_pylist() == expected,
            f"{name}: Arrow type or ordered signed slots")
    if observed.type == pa.date32():
        for day in expected:
            if day is not None and abs(day) < 100000:
                require(pa.array([day], type=pa.int32()).view(pa.date32())[0].as_py()
                        == date(1970, 1, 1) + timedelta(days=day), f"{name}: Gregorian day {day}")
    return str(observed.type)


def fixtures():
    optional = producer(EDGE_DAYS, pa.date32(), True)
    required = [-1, 0, 11016]
    cases = (
        ("date_both_optional_v1", "PyArrow", optional, 0, EDGE_DAYS, pa.date32(), ".logicalAndConverted"),
        ("date_both_required_v2", "PyArrow", producer(required, pa.date32(), False, "2.0"),
         0, required, pa.date32(), ".logicalAndConverted"),
        ("date_second_group", "PyArrow", producer(EDGE_DAYS, pa.date32(), True, group_size=4),
         1, EDGE_DAYS[4:], pa.date32(), ".logicalAndConverted"),
        ("date_modern_only", "Thrift footer edit", with_annotations(optional, None, [6]),
         0, EDGE_DAYS, pa.date32(), ".logical"),
        ("date_converted_only", "Thrift footer edit", with_annotations(optional, 6, None),
         0, EDGE_DAYS, pa.date32(), ".converted"),
        ("date_conflicting_converted", "Thrift footer edit", with_annotations(optional, 17, [6]),
         0, EDGE_DAYS, pa.date32(), "(.convertedType 17)"),
        ("date_malformed_modern", "Thrift footer edit", with_annotations(optional, 6, [6, 6]),
         0, None, None, ".logicalDate"),
        ("date_nonempty_type", "Thrift footer edit", with_annotations(optional, 6, [(6, True)]),
         0, None, None, ".logicalDate"),
        ("date_wrong_column_path", "Thrift footer edit", with_annotations(optional, 6, [6], "other"),
         0, None, None, "(.snapshot (.invalidMetadata .columns))"),
        ("date_wrong_physical", "Thrift footer edit",
         with_annotations(producer([0, 1], pa.int64(), True), 6, [6]),
         0, None, None, ".notFlatInt32"),
        ("plain_optional_int32", "PyArrow", producer(EDGE_DAYS, pa.int32(), True),
         0, EDGE_DAYS, pa.int32(), ".missingAnnotation"),
        ("date_optional_crc", "PyArrow", producer(EDGE_DAYS, pa.date32(), True, crc=True),
         0, EDGE_DAYS, pa.date32(), "(.scan .crcUnsupported)"),
    )
    for name, provenance, wire, group, expected, arrow_type, result in cases:
        fields, _, _, _ = raw_leaf(wire)
        host = None if arrow_type is None else host_observation(name, wire, expected, arrow_type, group)
        yield name, wire, group, result, {
            "provenance": provenance,
            "bytes": len(wire),
            "sha256": hashlib.sha256(wire).hexdigest(),
            "raw_schema_fields": fields,
            "host_arrow_type": host,
            "signed_slots": expected,
        }


CIVIL = {
    -(2**31): (-5877641, 6, 23),
    -719528: (0, 1, 1),
    2**31 - 1: (5881580, 7, 11),
}
HARNESS = """\
module

meta import Silmaril.Formats.Parquet.Date.Defs

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Numeric.Gregorian (CivilDate)

private meta def observes (bytes : Bytes) (index : Nat) (tag : Date.Annotation)
    (days : List (Option Int)) (civil : List (Option CivilDate)) : Bool :=
  match Date.readGroup {} bytes index with
  | .ok result => result.binding.leaf.name == "date" && result.binding.annotation == tag &&
      result.rowCount == days.length && result.date32Slots.map (Option.map Int32.toInt) == days &&
      decide (result.civilSlots = civil)
  | .error _ => false

private meta def rejects (bytes : Bytes) (index : Nat) (error : Date.Error) : Bool :=
  match Date.readGroup {} bytes index with
  | .error actual => actual == error
  | .ok _ => false
"""


def lean_bytes(wire):
    entries = ", ".join(f"0x{value:02x}" for value in wire)
    return f"(Bytes.ofList [{entries}])"


def lean_days(days):
    return "[" + ", ".join("none" if value is None else f"some ({value})" for value in days) + "]"


def lean_civil(days):
    cells = []
    for day in days:
        if day is None:
            cells.append("none")
        else:
            civil = CIVIL.get(day)
            if civil is None:
                observed = date(1970, 1, 1) + timedelta(days=day)
                civil = observed.year, observed.month, observed.day
            cells.append("some ⟨" + ", ".join(map(str, civil)) + "⟩")
    return "[" + ", ".join(cells) + "]"


def lean_case(wire, group, result, days):
    if result in (".logical", ".logicalAndConverted", ".converted"):
        return f"#guard observes {lean_bytes(wire)} {group} {result} {lean_days(days)} {lean_civil(days)}"
    return f"#guard rejects {lean_bytes(wire)} {group} {result}"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--pyarrow-path", type=Path)
    parser.add_argument("--thrift-path", type=Path)
    args = parser.parse_args()
    for path in (args.pyarrow_path, args.thrift_path):
        if path is not None:
            sys.path.insert(0, str(path.resolve()))

    global pa, pq, TType, TCompactProtocol, TMemoryBuffer
    import pyarrow as pa
    import pyarrow.parquet as pq
    from thrift.Thrift import TType
    from thrift.protocol.TCompactProtocol import TCompactProtocol
    from thrift.transport.TTransport import TMemoryBuffer

    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    require(platform.python_implementation() == "CPython" and platform.python_version() == manifest["cpython"],
            "Use the pinned CPython")
    require(pa.__version__ == manifest["pyarrow"] and version("thrift") == manifest["thrift"],
            "Use the pinned PyArrow and Thrift")
    commands = [HARNESS]
    for name, wire, group, result, details in fixtures():
        require(details == manifest["fixtures"][name], f"{name}: pinned bytes or observations differ")
        commands.append(lean_case(wire, group, result, details["signed_slots"]))
        if name == "date_both_optional_v1":
            commands.append(f"#guard rejects {lean_bytes(wire)} 1 (.groupIndex 1)")
        print(f"{name}: {details['sha256']}", flush=True)
    with tempfile.TemporaryDirectory(prefix="silmaril-parquet-date-") as scratch:
        driver = Path(scratch) / "Fixtures.lean"
        driver.write_text("\n".join(commands) + "\n", encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(driver)], cwd=REPO, check=True)
    print(f"PASS {len(commands) - 1} checked Parquet DATE fixture cases")


if __name__ == "__main__":
    main()
