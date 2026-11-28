"""Regenerate and independently verify the pinned complete INT96 Parquet files."""

import argparse
from datetime import date
import hashlib
from importlib.metadata import version
from pathlib import Path
import platform
import runpy
import struct

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer


ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "data/parquet-int96-file"
READ_STRUCT = runpy.run_path(str(ROOT / "tests/formats/parquet-timestamp-leaf/"
                               "check-fixtures.py"))["read_struct"]
DAY_NS = 86_400_000_000_000
JULIAN_EPOCH = 2_440_588
GROUP_SIZE = 6
PAGE_SIZE = 3
MIN, MAX = -(2**63), 2**63 - 1
SHA256 = {
    "required-v1": "1873d1a0d1fb57a9a218d5368fe5873546c382dba1a3b8d985382ca00d9796c0",
    "optional-v2": "14de048ac588f526f96749f374f64dfd3344ecd0d063d07df8b180d445233989",
    "optional-v2-bad-word": "5d642d40813915111fb336da4cc74ab13fd3f14a1a859e7f8e66ba0e84bff08e",
}


def write_file(unit, nullable, counts, page_version):
    timestamp = pa.timestamp(unit)
    schema = pa.schema([pa.field("decoy", pa.int32(), nullable=False),
                        pa.field("legacy_ts", timestamp, nullable=nullable)])
    values = pa.array(counts, type=pa.int64()).view(timestamp)
    table = pa.Table.from_arrays([pa.array(range(len(counts)), type=pa.int32()), values], schema=schema)
    sink = pa.BufferOutputStream()
    pq.write_table(table, sink, version="2.6", data_page_version=page_version,
                   compression="NONE", use_deprecated_int96_timestamps=True, use_dictionary=False,
                   write_statistics=False, store_schema=False, row_group_size=GROUP_SIZE,
                   write_batch_size=PAGE_SIZE, data_page_size=1)
    return sink.getvalue().to_pybytes()


def frames(wire, column, page_type, nullable, counts, scale):
    start = column.data_page_offset
    stop = start + column.total_compressed_size
    memory = TMemoryBuffer(wire[start:stop])
    protocol = TCompactProtocol(memory)
    offsets = []
    while memory.cstringio_buf.tell() < stop - start:
        header_start = start + memory.cstringio_buf.tell()
        header = READ_STRUCT(protocol)
        body_start = start + memory.cstringio_buf.tell()
        assert header[1][1] == page_type and header[2][1] == header[3][1]
        body = memory.readAll(header[3][1])
        if page_type == 0:
            page = header[5][1]
            count = page[1][1]
            assert (page[2][1], page[3][1], page[4][1]) == (0, 3, 3)
            level_end = 4 + struct.unpack_from("<I", body)[0] if nullable else 0
        else:
            page = header[8][1]
            count = page[1][1]
            assert (page[3][1], page[4][1], page[6][1]) == (count, 0, 0)
            level_end = page[5][1]
        assert count == PAGE_SIZE
        index = len(offsets) * PAGE_SIZE
        expected = [value * scale for value in counts[index:index + count] if value is not None]
        expected_words = [(value % DAY_NS, JULIAN_EPOCH + value // DAY_NS) for value in expected]
        assert list(struct.iter_unpack("<Qi", body[level_end:])) == expected_words
        offsets.append((header_start, body_start + level_end))
    assert memory.cstringio_buf.tell() == stop - start and len(offsets) == 2
    return offsets


def read_ticks(file, index):
    return file.read_row_group(index, columns=["legacy_ts"], use_threads=False).column(0).cast(
        pa.int64()).to_pylist()


def verify(wire, unit, nullable, counts, page_type):
    file = pq.ParquetFile(pa.BufferReader(wire), coerce_int96_timestamp_unit=unit)
    selected = file.schema.column(1)
    assert (selected.name, selected.physical_type, selected.max_definition_level,
            selected.max_repetition_level) == ("legacy_ts", "INT96", int(nullable), 0)
    assert file.schema.column(0).physical_type == "INT32" and file.metadata.num_row_groups == 3
    offsets = []
    for index in range(file.metadata.num_row_groups):
        group = file.metadata.row_group(index)
        column = group.column(1)
        assert (column.physical_type, column.compression) == ("INT96", "UNCOMPRESSED")
        assert column.dictionary_page_offset is None and column.encodings == ("RLE", "PLAIN")
        expected = counts[index * GROUP_SIZE:(index + 1) * GROUP_SIZE]
        assert read_ticks(file, index) == expected
        offsets.append(frames(wire, column, page_type, nullable, expected, 1 if unit == "ns" else 1000))
        print(f"{unit} group {index}: {expected}")
    return offsets


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true", help="Write the verified pinned files")
    args = parser.parse_args()
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    old_day = (date(1500, 3, 1) - date(1970, 1, 1)).days
    v1 = [MIN, -DAY_NS - 1, -DAY_NS, -1, 0, MAX,
          11, -12, 13, -14, 15, -16, 21, 22, 23, 24, 25, 26]
    v2 = [old_day * (DAY_NS // 1000) + 1, None, -1001, 0, None, 13,
          None, -4, 5, None, 1, 10**16, 21, None, 23, 24, 25, None]
    required = write_file("ns", False, v1, "1.0")
    optional = write_file("us", True, v2, "2.0")
    verify(required, "ns", False, v1, 0)
    page_offsets = verify(optional, "us", True, v2, 3)
    header_offset, first_word = page_offsets[1][1]
    assert v2[9:12] == [None, 1, 10**16]
    bad_word = first_word + 12
    damaged = optional[:bad_word] + struct.pack("<Q", DAY_NS) + optional[bad_word + 8:]
    broken = pq.ParquetFile(pa.BufferReader(damaged), coerce_int96_timestamp_unit="us")
    assert read_ticks(broken, 0) == v2[:6] and read_ticks(broken, 2) == v2[12:]
    print(f"Invalid subday in group 1, column 1, page 1, header offset {header_offset}, slot 2")
    for name, wire in (("required-v1", required), ("optional-v2", optional),
                       ("optional-v2-bad-word", damaged)):
        digest = hashlib.sha256(wire).hexdigest()
        assert digest == SHA256[name], f"unexpected {name} SHA-256"
        path = DATA / (name + ".parquet")
        if args.write:
            path.write_bytes(wire)
        assert path.read_bytes() == wire, f"pinned bytes differ for {name}"
        print(f"{digest}  {path.name}")


if __name__ == "__main__":
    main()
