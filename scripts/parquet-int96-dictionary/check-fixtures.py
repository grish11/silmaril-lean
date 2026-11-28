"""Verify pinned PyArrow dictionary INT96 files and their exact corrupt controls."""

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
DATA = ROOT / "data/parquet-int96-dictionary"
DAY_NS = 86_400_000_000_000
JULIAN_EPOCH = 2_440_588
GROUP_SIZE = 6
SHA256 = {
    "dictionary-v1": "3ec7c9a73a4797597f2265f1f8c5ec7525f2fa780bf83e0c87ed87ef497e93ca",
    "dictionary-v2": "0ab225fd34b732117b82c2274ea5859d887965a5896f85317b9ff117ca60f498",
}


def check_fixture(read_struct, unit, page_version, counts):
    kind = pa.timestamp(unit)
    rows = pa.table({"legacy_ts": pa.array(counts, type=pa.int64()).view(kind)})
    buffer = pa.BufferOutputStream()
    pq.write_table(rows, buffer, data_page_version=page_version, version="2.6", use_dictionary=True,
                   compression="NONE", row_group_size=GROUP_SIZE, write_statistics=False,
                   use_deprecated_int96_timestamps=True, store_schema=False)
    wire = buffer.getvalue().to_pybytes()
    parquet = pq.ParquetFile(pa.BufferReader(wire), coerce_int96_timestamp_unit=unit)
    assert parquet.metadata.num_row_groups == 2
    group_offsets = []
    for group in range(2):
        values = parquet.read_row_group(group).column(0).cast(pa.int64()).to_pylist()
        assert values == counts[group * GROUP_SIZE:(group + 1) * GROUP_SIZE]
        chunk = parquet.metadata.row_group(group).column(0)
        assert (chunk.physical_type, chunk.compression) == ("INT96", "UNCOMPRESSED")
        start = chunk.dictionary_page_offset
        memory = TMemoryBuffer(wire[start:start + chunk.total_compressed_size])
        protocol = TCompactProtocol(memory)
        leading = read_struct(protocol)
        assert leading[1][1] == 2 and leading[2][1] == leading[3][1]
        dictionary = leading[7][1]
        dictionary_body = start + memory.cstringio_buf.tell()
        assert dictionary[2][1] == 0
        words = list(struct.iter_unpack("<Qi", memory.readAll(leading[3][1])))
        nanos = [(day - JULIAN_EPOCH) * DAY_NS + subday for subday, day in words]
        assert all(0 <= subday < DAY_NS for subday, _ in words)
        assert len(words) == dictionary[1][1] == 3
        assert set(nanos) == {value * (1 if unit == "ns" else 1_000)
                              for value in values if value is not None}
        assert start + memory.cstringio_buf.tell() == chunk.data_page_offset
        data = read_struct(protocol)
        assert data[1][1] == (0 if page_version == "1.0" else 3)
        assert (data[5][1][2][1] if page_version == "1.0" else data[8][1][4][1]) == 8
        body_start = start + memory.cstringio_buf.tell()
        body = memory.readAll(data[3][1])
        values_start = body_start + (data[8][1][5][1] if page_version == "2.0" else
                                     4 + struct.unpack_from("<I", body)[0])
        group_offsets.append((start, dictionary_body, chunk.data_page_offset, values_start))
        assert memory.cstringio_buf.tell() == chunk.total_compressed_size
        print(f"V{page_version[0]} group {group}: {values}; dictionary nanos in wire order {nanos}")
    return wire, group_offsets


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    options = parser.parse_args()
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    read_struct = runpy.run_path(str(ROOT / "tests/formats/parquet-timestamp-leaf/"
                                    "check-fixtures.py"))["read_struct"]
    v1, v1_offsets = check_fixture(read_struct, "ns", "1.0",
                  [-1001, None, -1, -1001, 0, -1, 3, -4, None, 3, 5, None])
    v2, offsets = check_fixture(read_struct, "us", "2.0",
                  [-2, None, -1, -2, 10**16, -1, 6, -7, None, 6, 8, None])

    assert v1_offsets[1][2:] == (133, 158) and v1[158:162] == bytes([2, 3, 0x84, 0])
    assert offsets[1] == (84, 98, 134, 160)
    assert v2[160:164] == bytes([2, 3, 0x84, 0])
    # Width two and packed-run header 3. Physical reference 2 is at
    # logical slot 3 after the first null, and replacing it by 3 is invalid.
    assert [(v2[162] >> (2 * index)) & 3 for index in range(4)] == [0, 1, 0, 2]
    assert (v2[162] | (3 << 4)) == 0xB4
    assert struct.unpack_from("<Qi", v2, 110)[0] == DAY_NS - 7000
    assert struct.pack("<Q", DAY_NS) == bytes([0, 0, 79, 145, 148, 78, 0, 0])
    assert v2[94] == 0 and v2[148] == 16
    print("V2 group 1: dictionary starts at 84, data page at 134, bad reference at logical slot 3")
    for name, wire in (("dictionary-v1", v1), ("dictionary-v2", v2)):
        digest = hashlib.sha256(wire).hexdigest()
        assert digest == SHA256[name]
        path = DATA / (name + ".parquet")
        if options.write:
            path.write_bytes(wire)
        assert path.read_bytes() == wire
        print(f"{digest}  {name}.parquet")


if __name__ == "__main__":
    main()
