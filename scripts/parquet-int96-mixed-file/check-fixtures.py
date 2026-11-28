"""Regenerate and verify multi-group INT96 files with genuine writer fallback."""

import argparse
from hashlib import sha256
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
DATA = ROOT / "data/parquet-int96-mixed-file"
CHUNK = runpy.run_path(str(ROOT / "scripts/parquet-int96-mixed/check-fixtures.py"))
THRIFT = CHUNK["THRIFT"]
SHA256 = {
    "fallback-v1": "80dd266b7688d348f693f79156bcaf95e769067698cb8768c562d20ef7201e48",
    "fallback-v2": "d67ed9717daa33b5a315f630bf18d621abd1afeeb3cefd5c738ffa32ca25aa08",
    "v1-word": "7d121b0840ce6f5298dcd109f671b66d942283a38ee61a2aa8b500bf633d9b00",
    "v2-overlap": "daba7cf575ce15db631af4c964dc59bfb4e56d99c810780c72392a3dce78d2a0",
    "v2-reference": "e404dc3f202d286bc9ae5c20ba18a29686ce3515b465df7911bd00a37cd55856",
    "v2-reordered": "cc06e5874dc4d597992dd06ac7d541c1f4cd3ccff37567821159ddf39628333a",
    "v2-unselected": "d633d67977c72530e666856e9a8db4b2feb67b61f0c40b3715bb8275e047b906",
}


def producer(page_version, unit, groups):
    counts = [value for group in groups for value in group]
    scalar = pa.array(counts, type=pa.int64()).view(pa.timestamp(unit))
    fields = [pa.field("decoy", pa.int32(), nullable=False), pa.field("legacy_ts", scalar.type)]
    table = pa.Table.from_arrays([pa.array(range(len(counts)), type=pa.int32()), scalar],
                                 schema=pa.schema(fields))
    sink = pa.BufferOutputStream()
    pq.write_table(table, sink, version="2.6", data_page_version=page_version, compression="NONE",
                   use_dictionary=["legacy_ts"], use_deprecated_int96_timestamps=True,
                   write_statistics=False, store_schema=False, row_group_size=len(groups[0]),
                   dictionary_pagesize_limit=36, write_batch_size=4, data_page_size=48)
    return sink.getvalue().to_pybytes()


def reader(wire, unit):
    return pq.ParquetFile(pa.BufferReader(wire), coerce_int96_timestamp_unit=unit)


def ticks(file, group):
    return file.read_row_group(group, columns=["legacy_ts"], use_threads=False).column(0).cast(
        pa.int64()).to_pylist()


def verify(wire, page_version, unit, groups):
    file = reader(wire, unit)
    assert file.metadata.num_row_groups == len(groups)
    assert file.metadata.num_rows == sum(map(len, groups))
    assert file.schema.column(0).physical_type == "INT32"
    leaf = file.schema.column(1)
    assert (leaf.physical_type, leaf.max_definition_level, leaf.max_repetition_level) == ("INT96", 1, 0)
    dictionaries = set()
    offsets = []
    scale = 1 if unit == "ns" else 1000
    data_type = 0 if page_version == "1.0" else 3
    for index, group in enumerate(groups):
        assert ticks(file, index) == group and len(group) == 24
        metadata = file.metadata.row_group(index).column(1)
        assert (metadata.compression, metadata.encodings, metadata.num_values) == (
            "UNCOMPRESSED", ("PLAIN", "RLE", "RLE_DICTIONARY"), len(group))
        start = metadata.dictionary_page_offset
        memory = TMemoryBuffer(wire[start:start + metadata.total_compressed_size])
        protocol = TCompactProtocol(memory)
        header, dictionary_body, payload = CHUNK["frame"](protocol, start)
        dictionary = list(dict.fromkeys(value for value in group[:8] if value is not None))
        assert header[1][1] == 2 and (header[7][1][1][1], header[7][1][2][1]) == (len(dictionary), 0)
        assert list(struct.iter_unpack("<Qi", payload)) == CHUNK["words"](
            value * scale for value in dictionary)
        dictionaries.add(tuple(dictionary))
        assert start + memory.cstringio_buf.tell() == metadata.data_page_offset
        cursor = 0
        frames = []
        for tag, count in zip((8, 8, 0, 0), (4, 4, 8, 8)):
            header_start = start + memory.cstringio_buf.tell()
            header, body_start, payload = CHUNK["frame"](protocol, start)
            assert header[1][1] == data_type
            expected = group[cursor:cursor + count]
            cursor += count
            info = header[5 if data_type == 0 else 8][1]
            if data_type == 0:
                assert (info[1][1], info[2][1], info[3][1], info[4][1]) == (count, tag, 3, 3)
                level_stop = 4 + struct.unpack_from("<I", payload)[0]
                levels = payload[4:level_stop]
            else:
                assert (info[1][1], info[2][1], info[3][1], info[4][1], info[6][1], info[7][1]) == (
                    count, expected.count(None), count, tag, 0, False)
                level_stop = info[5][1]
                levels = payload[:level_stop]
            assert len(levels) == 2 and levels[0] == 3
            assert [(levels[1] >> slot) & 1 for slot in range(count)] == [
                tick is not None for tick in expected]
            present = [value for value in expected if value is not None]
            values = payload[level_stop:]
            if tag == 8:
                width, run = values[:2]
                assert width in (1, 2) and run == 3 and len(values) == 2 + width
                packed = int.from_bytes(values[2:], "little")
                indices = [(packed >> (width * slot)) & (2**width - 1) for slot in range(len(present))]
                assert indices == [dictionary.index(value) for value in present]
            else:
                assert list(struct.iter_unpack("<Qi", values)) == CHUNK["words"](
                    value * scale for value in present)
            frames.append((header_start, body_start + level_stop))
        assert cursor == len(group) and memory.cstringio_buf.tell() == metadata.total_compressed_size
        offsets.append((start, dictionary_body, frames))
        print(f"V{page_version[0]} group {index} {unit}: dictionary frame {start}, "
              f"entries {dictionary}, data tags [8, 8, 0, 0], offsets {frames}")
    assert len(dictionaries) == len(groups)
    return file, offsets


def patch(wire, offset, value):
    return wire[:offset] + value + wire[offset + len(value):]


def require_read_error(read):
    try:
        read()
    except (pa.ArrowException, OSError):
        return
    raise AssertionError("damaged projection read succeeded")


def controls(v1, v2, second, v1_offsets, v2_offsets, groups1, groups2):
    start, _, frames = v1_offsets[1]
    assert (start, frames[2]) == (589, (708, 735))
    bad_word_offset = frames[2][1] + 12
    assert groups1[1][8:11] == [1101, None, 898]
    assert struct.unpack_from("<Qi", v1, bad_word_offset) == CHUNK["words"]([898])[0]
    bad_word = patch(v1, bad_word_offset, struct.pack("<Q", CHUNK["DAY_NS"]))

    start, _, frames = v2_offsets[1]
    assert (start, frames[1]) == (601, (680, 706))
    offset = frames[1][1]
    assert v2[offset:offset + 4] == bytes([2, 3, 0x06, 0])
    assert groups2[1][5] is None and len(groups2[1][4:8]) == 4
    bad_reference = patch(v2, offset + 2, bytes([0x36]))
    bad_reader = reader(bad_reference, "us")
    require_read_error(lambda: ticks(bad_reader, 1))

    for file, unit, groups in ((bad_word, "ns", groups1), (bad_reference, "us", groups2)):
        broken = reader(file, unit)
        assert all(ticks(broken, group) == groups[group] for group in (0, 2))

    decoy = second.metadata.row_group(1).column(0)
    damaged_decoy = patch(v2, decoy.data_page_offset, bytes([0xFF]) * decoy.total_compressed_size)
    selected_only = reader(damaged_decoy, "us")
    assert [ticks(selected_only, index) for index in range(3)] == groups2
    require_read_error(lambda: selected_only.read_row_group(1, columns=["decoy"], use_threads=False))

    def alias(metadata):
        earlier = THRIFT["column_metadata"](metadata, 0)
        later = THRIFT["column_metadata"](metadata, 1)
        assert earlier[7] == later[7]
        for field in (9, 11):
            later[field] = earlier[field]

    overlap = THRIFT["rewrite_footer"](v2, alias)
    aliased = reader(overlap, "us")
    a, b = [aliased.metadata.row_group(index).column(1) for index in (0, 1)]
    assert (a.dictionary_page_offset, a.total_compressed_size) == (
        b.dictionary_page_offset, b.total_compressed_size)

    def swap(metadata):
        entries = THRIFT["list_field"](metadata, 4)
        entries[0], entries[1] = entries[1], entries[0]

    reordered = THRIFT["rewrite_footer"](v2, swap)
    swapped = reader(reordered, "us")
    assert [ticks(swapped, index) for index in range(3)] == [groups2[1], groups2[0], groups2[2]]
    return {"v1-word": bad_word, "v2-reference": bad_reference, "v2-unselected": damaged_decoy,
            "v2-overlap": overlap, "v2-reordered": reordered}


def shifted(counts, shifts):
    return [[None if tick is None else tick + shift for tick in counts] for shift in shifts]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    counts = CHUNK["COUNTS"]
    groups1 = shifted(counts, (0, 1000, -2000))
    groups2 = shifted(counts[:7] + [-1] + counts[8:], (0, 10**16, -10**16))
    v1 = producer("1.0", "ns", groups1)
    v2 = producer("2.0", "us", groups2)
    _, v1_offsets = verify(v1, "1.0", "ns", groups1)
    second, v2_offsets = verify(v2, "2.0", "us", groups2)
    fixtures = {"fallback-v1": v1, "fallback-v2": v2,
                **controls(v1, v2, second, v1_offsets, v2_offsets, groups1, groups2)}
    for name, wire in fixtures.items():
        digest = sha256(wire).hexdigest()
        assert digest == SHA256[name], f"unexpected {name} SHA-256"
        path = DATA / (name + ".parquet")
        if args.write:
            path.write_bytes(wire)
        assert path.read_bytes() == wire
        print(f"{digest}  {path.name}")


if __name__ == "__main__":
    main()
