"""Prove fixture provenance by regenerating PyArrow fallback files and checking their wire."""

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
DATA = ROOT / "data/parquet-int96-mixed"
THRIFT = runpy.run_path(str(ROOT / "tests/formats/parquet-timestamp-leaf/check-fixtures.py"))
DAY_NS = 86_400_000_000_000
JULIAN_EPOCH = 2_440_588
COUNTS = [-1, None, 17, -1, 3, None, 17, 19, 101, None, -102, 103, 104,
          None, -105, 106, 107, None, 108, 109, 110, 111, None, 113]
DICTIONARY = [-1, 17, 3, 19]
FRAMES = {
    "1.0": ((4, 18), [(66, 91), (94, 119), (123, 150), (222, 249)]),
    "2.0": ((4, 18), [(66, 92), (95, 121), (125, 153), (225, 253)]),
}
SHA256 = {
    "fallback-v1": "7abfedd62723f30a8f88f85fa0fa481467c3e132136d23a6249314ed529f934f",
    "fallback-v2": "156b58ede395a3ce181dac40e4fec74ebfcb802e2abd3dd2302c7ec62b08f707",
    "v1-bad-plain-word": "a8585d08f40f8def2400672af575f9fdca2fdb4b5e33fcde26a15dddab43986c",
    "v2-bad-reference": "7b52b93c532c86e5da43d86bc59c444389033cfcf77c49db52990727212dbf42",
}


def producer(page_version):
    scalar = pa.array(COUNTS, type=pa.int64()).view(pa.timestamp("ns"))
    table = pa.table({"legacy_ts": scalar})
    sink = pa.BufferOutputStream()
    pq.write_table(table, sink, version="2.6", data_page_version=page_version, compression="NONE",
                   use_dictionary=True, use_deprecated_int96_timestamps=True, write_statistics=False,
                   store_schema=False, row_group_size=len(COUNTS), dictionary_pagesize_limit=36,
                   write_batch_size=4, data_page_size=48)
    return sink.getvalue().to_pybytes()


def reader(wire):
    return pq.ParquetFile(pa.BufferReader(wire), coerce_int96_timestamp_unit="ns")


def words(values):
    return [(value % DAY_NS, JULIAN_EPOCH + value // DAY_NS) for value in values]


def frame(protocol, start):
    header = THRIFT["read_struct"](protocol)
    memory = protocol.trans
    body_start = start + memory.cstringio_buf.tell()
    assert header[2][1] == header[3][1] and 4 not in header
    return header, body_start, memory.readAll(header[3][1])


def verify(wire, page_version):
    file = reader(wire)
    assert file.read().column(0).cast(pa.int64()).to_pylist() == COUNTS
    leaf = file.schema.column(0)
    assert (leaf.physical_type, leaf.max_repetition_level, leaf.max_definition_level) == ("INT96", 0, 1)
    assert file.metadata.num_row_groups == 1
    chunk = file.metadata.row_group(0).column(0)
    assert (chunk.compression, chunk.encodings, chunk.num_values) == (
        "UNCOMPRESSED", ("PLAIN", "RLE", "RLE_DICTIONARY"), len(COUNTS))
    start = chunk.dictionary_page_offset
    memory = TMemoryBuffer(wire[start:start + chunk.total_compressed_size])
    protocol = TCompactProtocol(memory)
    header, dictionary_body, payload = frame(protocol, start)
    assert header[1][1] == 2 and header[7][1][1][1] == 4 and header[7][1][2][1] == 0
    assert list(struct.iter_unpack("<Qi", payload)) == words(DICTIONARY)
    assert (start, dictionary_body) == FRAMES[page_version][0]
    assert start + memory.cstringio_buf.tell() == chunk.data_page_offset
    print(f"V{page_version[0]} dictionary frame at {start}, four PLAIN entries {DICTIONARY}")

    cursor = 0
    data_type = 0 if page_version == "1.0" else 3
    for ordinal, (encoding, count) in enumerate(zip((8, 8, 0, 0), (4, 4, 8, 8)), 1):
        offset = start + memory.cstringio_buf.tell()
        header, body_start, payload = frame(protocol, start)
        assert header[1][1] == data_type
        expected = COUNTS[cursor:cursor + count]
        cursor += count
        if page_version == "1.0":
            info = header[5][1]
            assert (info[1][1], info[2][1], info[3][1], info[4][1]) == (count, encoding, 3, 3)
            level_size = struct.unpack_from("<I", payload)[0]
            levels = payload[4:4 + level_size]
            data_offset = 4 + level_size
        else:
            info = header[8][1]
            assert (info[1][1], info[2][1], info[3][1], info[4][1], info[6][1], info[7][1]) == (
                count, expected.count(None), count, encoding, 0, False)
            data_offset = info[5][1]
            levels = payload[:data_offset]
        # These pinned masks each use one width-one bit-packed group.
        assert len(levels) == 2 and levels[0] == 3
        assert [(levels[1] >> slot) & 1 for slot in range(count)] == [
            value is not None for value in expected]
        present = [value for value in expected if value is not None]
        values = payload[data_offset:]
        assert (offset, body_start + data_offset) == FRAMES[page_version][1][ordinal - 1]
        if encoding == 8:
            width, header = values[:2]
            assert width in (1, 2) and header == 3 and len(values) == 2 + width
            packed = int.from_bytes(values[2:], "little")
            indices = [(packed >> (width * slot)) & (2**width - 1) for slot in range(len(present))]
            assert indices == [DICTIONARY.index(value) for value in present]
        else:
            assert list(struct.iter_unpack("<Qi", values)) == words(present)
        print(f"V{page_version[0]} data frame {ordinal} at {offset}, encoding {encoding}, slots {expected}")
    assert cursor == len(COUNTS) and memory.cstringio_buf.tell() == chunk.total_compressed_size


def bad_plain_word(wire):
    # The second present word of the first PLAIN page is at logical slot 2.
    offset = FRAMES["1.0"][1][2][1] + 12
    assert COUNTS[8:11] == [101, None, -102]
    assert struct.unpack_from("<Qi", wire, offset) == words([-102])[0]
    changed = wire[:offset] + struct.pack("<Q", DAY_NS) + wire[offset + 8:]
    assert struct.unpack_from("<Q", changed, offset)[0] == DAY_NS
    return changed


def bad_reference(wire):
    # Keep each original data page. Remove dictionary entry 3 so the second
    # dictionary data page's final reference fails at logical slot 3.
    start, dictionary_body = FRAMES["2.0"][0]
    memory = TMemoryBuffer(wire[start:dictionary_body])
    header = THRIFT["read_struct"](TCompactProtocol(memory))
    header[2] = header[2][0], 36
    header[3] = header[3][0], 36
    dictionary = header[7][1]
    dictionary[1] = dictionary[1][0], 3
    new_header = THRIFT["encode"](header)
    assert len(new_header) == dictionary_body - start
    removed = dictionary_body + 36
    changed = wire[:start] + new_header + wire[dictionary_body:removed] + wire[removed + 12:]

    def rebase_footer(metadata):
        group = THRIFT["list_field"](metadata, 4)[0]
        column = THRIFT["column_metadata"](metadata, 0, 0)
        for fields, keys in ((group, (2, 6)), (column, (6, 7, 9))):
            for field in keys:
                kind, value = fields[field]
                fields[field] = kind, value - 12

    changed = THRIFT["rewrite_footer"](changed, rebase_footer)
    column = reader(changed).metadata.row_group(0).column(0)
    assert (column.dictionary_page_offset, column.data_page_offset) == (4, 54)
    second_header, values = FRAMES["2.0"][1][1]
    assert second_header - 12 == 83
    assert changed[values - 12:values - 8] == bytes([2, 3, 0x36, 0])
    assert changed[54:4 + column.total_compressed_size] == wire[66:4 + column.total_compressed_size + 12]
    assert COUNTS[4:8] == [3, None, 17, 19]
    try:
        reader(changed).read()
    except (pa.ArrowException, OSError):
        pass
    else:
        raise AssertionError("PyArrow accepted the bad dictionary reference")
    return changed


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    v1 = producer("1.0")
    v2 = producer("2.0")
    verify(v1, "1.0")
    verify(v2, "2.0")
    for name, wire in (("fallback-v1", v1), ("fallback-v2", v2),
                       ("v1-bad-plain-word", bad_plain_word(v1)), ("v2-bad-reference", bad_reference(v2))):
        digest = sha256(wire).hexdigest()
        assert digest == SHA256[name], f"unexpected {name} SHA-256"
        path = DATA / (name + ".parquet")
        if args.write:
            path.write_bytes(wire)
        assert path.read_bytes() == wire
        print(f"{digest}  {path.name}")


if __name__ == "__main__":
    main()
