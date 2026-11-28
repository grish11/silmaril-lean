"""Regenerate and independently check selected-leaf INT96 dictionary files."""

import argparse
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
DATA = ROOT / "data/parquet-int96-dictionary-file"
THRIFT = runpy.run_path(str(ROOT / "tests/formats/parquet-timestamp-leaf/check-fixtures.py"))
DAY_NS = 86_400_000_000_000
JULIAN_EPOCH = 2_440_588
ROWS = 6
SHA256 = {
    "optional-v2": "12fa8048830198caea7b7d1373642f2ba16a7c16026babf4f5b8ae48c6e12a9d",
    "required-v1": "54b61503be406fefaabc16ba7d4197ddb8fb1fa5dd43bd90c56b5549d3d57b0e",
    "v2-overlap": "2e4238e7da04164c234a6a7f2d5482e19969674a8578a9c2327650f4d7f08659",
    "v2-reference": "b7806b284df3f04aa00dbdf4156041e3cf37474ce9e463e1b63adba7e50150e0",
    "v2-reordered": "87d2c6e9f87cd30ee8cf9ee085451e5e51c923ff6106671f0843657da13b539d",
    "v2-unselected": "c3ae3071da92f889891d1adb46ad7de0596f7a5f918b5ca6ea1e35e53d8e3f5e",
    "v2-word": "472221cfd4a1aeb2cf17e0ad29bfd459af312cccaae5f46e552e7771aa3f7a8a",
}


def producer(unit, nullable, page_version, counts):
    timestamp = pa.timestamp(unit)
    schema = pa.schema([pa.field("decoy", pa.int32(), nullable=False),
                        pa.field("legacy_ts", timestamp, nullable=nullable)])
    table = pa.Table.from_arrays([pa.array(range(len(counts)), type=pa.int32()),
                                 pa.array(counts, type=pa.int64()).view(timestamp)], schema=schema)
    sink = pa.BufferOutputStream()
    pq.write_table(table, sink, version="2.6", data_page_version=page_version, compression="NONE",
                   use_dictionary=["legacy_ts"], use_deprecated_int96_timestamps=True,
                   write_statistics=False, store_schema=False, row_group_size=ROWS)
    return sink.getvalue().to_pybytes()


def reader(wire, unit):
    return pq.ParquetFile(pa.BufferReader(wire), coerce_int96_timestamp_unit=unit)


def ticks(file, group):
    return file.read_row_group(group, columns=["legacy_ts"], use_threads=False).column(0).cast(
        pa.int64()).to_pylist()


def verify(wire, unit, nullable, page_type, counts):
    file = reader(wire, unit)
    leaf = file.schema.column(1)
    assert (leaf.name, leaf.physical_type, leaf.max_definition_level, leaf.max_repetition_level) == (
        "legacy_ts", "INT96", int(nullable), 0)
    assert file.schema.column(0).physical_type == "INT32"
    assert file.metadata.num_row_groups == 3
    offsets = []
    dictionaries = []
    for index in range(3):
        expected = counts[index * ROWS:(index + 1) * ROWS]
        assert ticks(file, index) == expected
        column = file.metadata.row_group(index).column(1)
        assert (column.physical_type, column.compression, column.encodings) == (
            "INT96", "UNCOMPRESSED", ("PLAIN", "RLE", "RLE_DICTIONARY"))
        start = column.dictionary_page_offset
        stop = start + column.total_compressed_size
        memory = TMemoryBuffer(wire[start:stop])
        protocol = TCompactProtocol(memory)
        dictionary = THRIFT["read_struct"](protocol)
        words_start = start + memory.cstringio_buf.tell()
        assert dictionary[1][1] == 2 and dictionary[2][1] == dictionary[3][1] == 36
        assert dictionary[7][1][1][1] == 3 and dictionary[7][1][2][1] == 0
        words = list(struct.iter_unpack("<Qi", memory.readAll(36)))
        scale = 1 if unit == "ns" else 1000
        present = [value * scale for value in expected if value is not None]
        distinct = list(dict.fromkeys(present))
        assert words == [(value % DAY_NS, JULIAN_EPOCH + value // DAY_NS) for value in distinct]
        dictionaries.append(distinct)
        data_start = start + memory.cstringio_buf.tell()
        assert data_start == column.data_page_offset
        data = THRIFT["read_struct"](protocol)
        body_start = start + memory.cstringio_buf.tell()
        assert data[1][1] == page_type and data[2][1] == data[3][1]
        body = memory.readAll(data[3][1])
        if page_type == 0:
            header = data[5][1]
            assert (header[1][1], header[2][1], header[3][1], header[4][1]) == (ROWS, 8, 3, 3)
            levels = 4 + struct.unpack_from("<I", body)[0] if nullable else 0
        else:
            header = data[8][1]
            assert (header[1][1], header[2][1], header[3][1], header[4][1],
                    header[6][1]) == (ROWS, expected.count(None), ROWS, 8, 0)
            levels = header[5][1]
        indices = body[levels:]
        assert indices[:2] == bytes([2, 3]) and len(indices) == 4
        packed = int.from_bytes(indices[2:], "little")
        assert [(packed >> (2 * ref)) & 3 for ref in range(len(present))] == [
            distinct.index(value) for value in present]
        assert start + memory.cstringio_buf.tell() == stop
        offsets.append((start, words_start, data_start, body_start + levels))
        print(f"{unit} group {index}: {expected}; dictionary nanos {distinct}; offsets {offsets[-1]}")
    assert len({tuple(dictionary) for dictionary in dictionaries}) == 3
    return file, offsets


def put(wire, offset, value):
    return wire[:offset] + value + wire[offset + len(value):]


def check_controls(wire, file, offsets, counts):
    start, words, data, indices = offsets[1]
    assert wire[indices:indices + 4] == bytes([2, 3, 0x84, 0])
    assert counts[ROWS:2 * ROWS] == [6, -7, None, 6, 8, None]
    bad_reference = put(wire, indices + 2, bytes([0xB4]))
    bad_word = put(wire, words + 12, struct.pack("<Q", DAY_NS))
    assert struct.unpack_from("<Q", wire, words + 12)[0] == DAY_NS - 7000
    for damaged in (bad_reference, bad_word):
        broken = reader(damaged, "us")
        assert ticks(broken, 0) == counts[:ROWS]
        assert ticks(broken, 2) == counts[2 * ROWS:]
    try:
        ticks(reader(bad_reference, "us"), 1)
    except (pa.ArrowException, OSError):
        pass
    else:
        raise AssertionError("group 1 out-of-range reference was accepted by PyArrow")

    decoy = file.metadata.row_group(1).column(0)
    decoy_start = decoy.data_page_offset
    unselected = put(wire, decoy_start, bytes([0xFF]) * decoy.total_compressed_size)
    projected = reader(unselected, "us")
    assert [ticks(projected, group) for group in range(3)] == [
        counts[group * ROWS:(group + 1) * ROWS] for group in range(3)]
    try:
        projected.read_row_group(1, columns=["decoy"], use_threads=False)
    except (pa.ArrowException, OSError):
        pass
    else:
        raise AssertionError("damage did not break the unselected column")

    def alias(metadata):
        earlier = THRIFT["column_metadata"](metadata, 0)
        later = THRIFT["column_metadata"](metadata, 1)
        for field in (9, 11):  # data_page_offset, dictionary_page_offset
            later[field] = earlier[field]

    overlap = THRIFT["rewrite_footer"](wire, alias)
    aliased = reader(overlap, "us")
    old, new = [aliased.metadata.row_group(group).column(1) for group in (0, 1)]
    assert old.dictionary_page_offset == new.dictionary_page_offset
    assert old.data_page_offset == new.data_page_offset
    assert old.total_compressed_size == new.total_compressed_size > 0
    def swap_groups(metadata):
        groups = THRIFT["list_field"](metadata, 4)
        groups[0], groups[1] = groups[1], groups[0]

    reordered = THRIFT["rewrite_footer"](wire, swap_groups)
    swapped = reader(reordered, "us")
    assert [ticks(swapped, group) for group in range(3)] == [
        counts[ROWS:2 * ROWS], counts[:ROWS], counts[2 * ROWS:]]
    print(f"Bad V2 reference at logical slot 3, chunk {start}, header {data}; "
          f"bad dictionary entry 1; unselected damage at {decoy_start}; selected interval alias")
    return {"v2-reference": bad_reference, "v2-word": bad_word,
            "v2-unselected": unselected, "v2-overlap": overlap, "v2-reordered": reordered}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    minimum, maximum = -(2**63), 2**63 - 1
    v1_counts = [minimum, -1, maximum, -1, minimum, maximum,
                 6, -7, 8, 6, -7, 8, 11, 12, 13, 11, 12, 13]
    v2_counts = [-2, None, -1, -2, 10**16, -1,
                 6, -7, None, 6, 8, None, None, 0, 21, 22, None, 21]
    v1 = producer("ns", False, "1.0", v1_counts)
    v2 = producer("us", True, "2.0", v2_counts)
    verify(v1, "ns", False, 0, v1_counts)
    file, offsets = verify(v2, "us", True, 3, v2_counts)
    fixtures = {"required-v1": v1, "optional-v2": v2, **check_controls(v2, file, offsets, v2_counts)}
    for name, wire in fixtures.items():
        digest = hashlib.sha256(wire).hexdigest()
        assert digest == SHA256[name], f"unexpected {name} SHA-256"
        path = DATA / (name + ".parquet")
        if args.write:
            path.write_bytes(wire)
        assert path.read_bytes() == wire
        print(f"{digest}  {path.name}")


if __name__ == "__main__":
    main()
