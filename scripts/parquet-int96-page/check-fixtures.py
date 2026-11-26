"""Verify the pinned PyArrow files and reproduce the exact framed Lean fixtures."""

import argparse
from datetime import date
import hashlib
from importlib.metadata import version
from pathlib import Path
import platform
import runpy
import struct
import textwrap

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer


ROOT = Path(__file__).resolve().parents[2]
LEAN_TESTS = ROOT / "Silmaril/Formats/Parquet/Int96/Page/Tests.lean"
BEGIN = "-- BEGIN pinned PyArrow frames"
END = "-- END pinned PyArrow frames"
DAY_NS = 86_400_000_000_000
EPOCH_JULIAN_DAY = 2_440_588
I64_MIN, I64_MAX = -(2**63), 2**63 - 1
SHA256 = {
    "v1-nanoseconds": "1c0e0f3d25c34165d556417bd665bf9dc6d90cfe4fa5f83348c98e29a4d95415",
    "v2-invalid-subday": "7768e78ec07b8927ff4f74cd3936accf8733caa882557833ecd8997fc6cc5726",
    "v2-microseconds": "d2fbc3374c77c67137d0a48e9f3bc4ab30d246e1fd9af3a605a11664f696a3dc",
}


def plain_page(wire, column, page_type, read_struct):
    start = column.data_page_offset
    length = column.total_compressed_size
    memory = TMemoryBuffer(wire[start:start + length])
    header = read_struct(TCompactProtocol(memory))
    body_start = start + memory.cstringio_buf.tell()
    assert header[1][1] == page_type and header[2][1] == header[3][1]
    assert body_start + header[3][1] == start + length
    if page_type == 0:
        page = header[5][1]
        assert page[2][1] == 0 and page[1][1] == column.num_values
        level_bytes, = struct.unpack_from("<I", wire, body_start)
        scalar_start = body_start + 4 + level_bytes
    else:
        page = header[8][1]
        assert page[4][1] == 0 and page[3][1] == column.num_values and page[6][1] == 0
        scalar_start = body_start + page[5][1]
    return scalar_start, wire[scalar_start:start + length]


def produce(unit, counts, page_version):
    timestamp = pa.timestamp(unit)
    schema = pa.schema([pa.field("legacy_ts", timestamp, nullable=True)])
    array = pa.array(counts, type=pa.int64()).view(timestamp)
    sink = pa.BufferOutputStream()
    pq.write_table(pa.Table.from_arrays([array], schema=schema), sink, row_group_size=4,
                   version="2.6", data_page_version=page_version, compression="NONE",
                   use_deprecated_int96_timestamps=True, use_dictionary=False,
                   write_statistics=False, store_schema=False)
    return sink.getvalue().to_pybytes()


def verify(wire, unit, counts, page_type, read_struct):
    parquet = pq.ParquetFile(pa.BufferReader(wire), coerce_int96_timestamp_unit=unit)
    assert parquet.metadata.num_row_groups == 2
    actual = []
    offsets = []
    frames = []
    for group in range(parquet.metadata.num_row_groups):
        column = parquet.metadata.row_group(group).column(0)
        assert (column.physical_type, column.compression) == ("INT96", "UNCOMPRESSED")
        assert column.dictionary_page_offset is None and column.encodings == ("RLE", "PLAIN")
        rows = parquet.read_row_group(group, use_threads=False).column(0).cast(pa.int64()).to_pylist()
        expected = counts[group * 4:(group + 1) * 4]
        assert rows == expected
        start, scalars = plain_page(wire, column, page_type, read_struct)
        physical_words = list(struct.iter_unpack("<Qi", scalars))
        coordinates = [count * (1 if unit == "ns" else 1_000) for count in rows if count is not None]
        expected_words = [(ns % DAY_NS, EPOCH_JULIAN_DAY + ns // DAY_NS) for ns in coordinates]
        assert physical_words == expected_words
        actual.append(rows)
        offsets.append(start)
        frame_start = column.data_page_offset
        frames.append(wire[frame_start:frame_start + column.total_compressed_size])
    return actual, offsets, frames


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--emit-frames", action="store_true", help="Print the verified Lean fixture block")
    args = parser.parse_args()
    assert platform.python_version() == "3.13.5" and platform.python_implementation() == "CPython"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    read_struct = runpy.run_path(str(ROOT / "tests/formats/parquet-timestamp-leaf/"
                                    "check-fixtures.py"))["read_struct"]
    old_day = (date(1500, 3, 1) - date(1970, 1, 1)).days
    cases = {
        "v1-nanoseconds": ("ns", [I64_MIN, -DAY_NS - 1, None, -1, 0, 1, I64_MAX], "1.0", 0),
        "v2-microseconds": ("us", [old_day * (DAY_NS // 1_000) + 1, None, -1001, 0,
                                  None, 1, 10**16], "2.0", 3),
    }
    files = {}
    lean_frames = {}
    for name, (unit, counts, page_version, page_type) in cases.items():
        wire = produce(unit, counts, page_version)
        groups, offsets, frames = verify(wire, unit, counts, page_type, read_struct)
        for index, frame in enumerate(frames):
            lean_frames[f"v{page_version[0]}Group{index}"] = frame
        if not args.emit_frames:
            print(f"{name} signed row groups {groups}")
        files[name] = wire
        if name == "v2-microseconds":
            offset = offsets[1] + 12  # Second present word, logical slot two
            bad = wire[:offset] + struct.pack("<Q", DAY_NS) + wire[offset + 8:]
            assert len(bad) == len(wire) and struct.unpack_from("<Q", bad, offset)[0] == DAY_NS
            parquet = pq.ParquetFile(pa.BufferReader(bad), coerce_int96_timestamp_unit=unit)
            assert parquet.read_row_group(0).column(0).cast(pa.int64()).to_pylist() == groups[0]
            # The invalid word has a nanos-of-day equal to one full day. This
            # violates the payload contract even if a reader normalizes it.
            files["v2-invalid-subday"] = bad
            chunk = parquet.metadata.row_group(1).column(0)
            start = chunk.data_page_offset
            lean_frames["v2BadGroup1"] = bad[start:start + chunk.total_compressed_size]
            if not args.emit_frames:
                print(f"v2-invalid-subday: logical slot 2 has nanos-of-day {DAY_NS}")
    for name, wire in files.items():
        digest = hashlib.sha256(wire).hexdigest()
        assert digest == SHA256[name]
        if not args.emit_frames:
            print(f"{digest}  {name}.parquet")
    lines = [BEGIN]
    for name, frame in lean_frames.items():
        octets = textwrap.fill(str(list(frame)), width=96, initial_indent="  ", subsequent_indent="   ")
        lines.extend([f"private def {name} : List UInt8 :=", octets])
    expected = "\n".join([*lines, END])
    if args.emit_frames:
        print(expected)
    else:
        tests = LEAN_TESTS.read_text(encoding="utf-8")
        actual = tests[tests.index(BEGIN):tests.index(END) + len(END)]
        assert actual == expected, "Embedded Lean frames differ from the pinned PyArrow pages"
        print("Matched the five exact PageHeader and payload frames used by the Lean guards")


if __name__ == "__main__":
    main()
