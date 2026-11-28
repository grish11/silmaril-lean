"""Compare ordered timestamp events with pinned independent PyArrow row groups."""

import hashlib
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
from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
THRIFT = runpy.run_path(str(HERE.parent / "parquet-timestamp-leaf" / "check-fixtures.py"))
UNITS = {"ms": "millisecond", "us": "microsecond", "ns": "nanosecond"}
MIN, MAX = -(2**63), 2**63 - 1


def produce(name, unit, adjusted, nullable, groups):
    timestamp = pa.timestamp(unit, "UTC" if adjusted else None)
    schema = pa.schema([pa.field(name, timestamp, nullable=nullable)])
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, version="2.6", data_page_version="2.0",
                          compression="NONE", column_encoding="PLAIN", use_dictionary=False,
                          write_statistics=False, store_schema=False) as writer:
        for group in groups:
            array = pa.array(group, type=pa.int64()).view(timestamp)
            writer.write_table(pa.Table.from_arrays([array], schema=schema))
    return sink.getvalue().to_pybytes()


def frame_empty_group(wire):
    # PyArrow writes the empty group's footer entry without a data page.
    # Add one zero-row PLAIN V2 page so the checked binder has a real span.
    zero = TType.I32, 0
    page = THRIFT["encode"]({
        1: (TType.I32, 3), 2: zero, 3: zero,
        8: (TType.STRUCT, {**dict.fromkeys(range(1, 7), zero), 7: (TType.BOOL, False)}),
    })
    size, = struct.unpack_from("<I", wire, len(wire) - 8)
    start = len(wire) - 8 - size

    def attach(metadata):
        group = THRIFT["list_field"](metadata, 4)[1]
        column = THRIFT["column_metadata"](metadata, group=1, column=0)
        assert group[3] == column[5] == column[7] == column[9] == (TType.I64, 0)
        group[2] = group[6] = TType.I64, len(page)
        column[6] = column[7] = TType.I64, len(page)
        column[9] = TType.I64, start

    return THRIFT["rewrite_footer"](wire[:start] + page + wire[start:], attach)


def damage_last_page(wire, parquet):
    start = parquet.metadata.row_group(2).column(0).data_page_offset
    memory = TMemoryBuffer(wire[start:])
    page = THRIFT["read_struct"](TCompactProtocol(memory))
    size = memory.cstringio_buf.tell()
    header = page[8][1]
    assert header[4] == (TType.I32, 0)
    header[4] = TType.I32, 8  # RLE_DICTIONARY, without a dictionary
    replacement = THRIFT["encode"](page)
    assert len(replacement) == size
    return wire[:start] + replacement + wire[start + size:]


def read_group(parquet, index):
    values = parquet.read_row_group(index, use_threads=False).column(0)
    return values.cast(pa.int64()).to_pylist()


def lean_groups(groups):
    return "[" + ", ".join(map(THRIFT["lean_ticks"], groups)) + "]"


def fixtures(directory):
    files = {}
    lines = ["private def fixtures : IO Unit := do"]
    for unit, lean_unit in UNITS.items():
        for adjusted in (False, True):
            name = unit + ("_utc" if adjusted else "_local")
            nullable = name != "ns_utc"
            groups = [[MIN, -2001, None if nullable else -1], [], [0, MAX, -17]]
            wire = frame_empty_group(produce(name, unit, adjusted, nullable, groups))
            parquet = pq.ParquetFile(pa.BufferReader(wire))
            leaf = parquet.schema.column(0)
            logical = json.loads(leaf.logical_type.to_json())
            assert (leaf.name, logical["Type"], logical["isAdjustedToUTC"]) == (name, "Timestamp", adjusted)
            field = parquet.schema_arrow.field(0)
            assert field.type == pa.timestamp(unit, "UTC" if adjusted else None)
            assert field.nullable == nullable and parquet.metadata.num_row_groups == 3
            observed = [read_group(parquet, index) for index in range(3)]
            assert observed == groups
            files[name] = wire
            path = json.dumps(str(directory / (name + ".parquet")))
            timezone = '(some "UTC")' if adjusted else "none"
            lines.append(f'  checkFixture {path} "{name}" .{lean_unit} {timezone} '
                         f'{str(nullable).lower()} {lean_groups(observed)}')

            if name == "us_local":
                damaged = damage_last_page(wire, parquet)
                broken = pq.ParquetFile(pa.BufferReader(damaged))
                assert [read_group(broken, index) for index in range(2)] == observed[:2]
                try:
                    read_group(broken, 2)
                except (pa.ArrowInvalid, pa.ArrowNotImplementedError, OSError):
                    pass
                else:
                    raise AssertionError("PyArrow accepted the damaged later group")
                files["damaged"] = damaged
                path = json.dumps(str(directory / "damaged.parquet"))
                lines.append(f'  checkDamaged {path} "{name}" {lean_groups(observed[:2])}')
    return files, lines


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    with tempfile.TemporaryDirectory() as temporary:
        directory = Path(temporary)
        files, lines = fixtures(directory)
        observed = {}
        for name, wire in sorted(files.items()):
            observed[name] = hashlib.sha256(wire).hexdigest()
            (directory / (name + ".parquet")).write_bytes(wire)
        assert pins == observed, f"fixture SHA-256 values differ: {json.dumps(observed, indent=2)}"
        driver = directory / "Fixture.lean"
        oracle = (HERE / "Oracle.lean").read_text(encoding="utf-8")
        driver.write_text(oracle + "\n" + "\n".join([*lines, "#eval fixtures"]) + "\n", encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(driver)], cwd=ROOT, check=True)
    print("PyArrow 26.0.1 and Thrift 0.25.0: six ordered three-group traces and one typed late failure passed")
    print("Exact schema, 18 batches (six empty), collected rows, bounded close and typed open failure passed")


if __name__ == "__main__":
    main()
