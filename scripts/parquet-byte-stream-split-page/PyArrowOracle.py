"""Extract exact nullable BYTE_STREAM_SPLIT V1/V2 bodies from PyArrow 26.0.1."""

from pathlib import Path
from runpy import run_path
import struct

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

page_oracle = run_path(
    str(Path(__file__).resolve().parents[1] / "parquet-scalar-page" / "PyArrowOracle.py")
)
header_fields = page_oracle["header_fields"]
footer_codec = page_oracle["footer_codec"]


def emit(version, name, physical, dtype, width, words, present, compression="NONE"):
    assert len(words) == sum(present) and all(len(word) == width for word in words)
    count = len(present)
    nulls = count - len(words)
    validity = sum(int(flag) << index for index, flag in enumerate(present))
    bitmap = validity.to_bytes((count + 7) // 8, "little")
    remaining = iter(words)
    unstriped = b"".join(next(remaining) if flag else bytes(width) for flag in present)
    array = pa.Array.from_buffers(dtype, count, [pa.py_buffer(bitmap), pa.py_buffer(unstriped)], nulls)
    schema = pa.schema([pa.field("v", dtype, nullable=True)])
    sink = pa.BufferOutputStream()
    pq.write_table(
        pa.Table.from_arrays([array], schema=schema), sink, version="2.6", data_page_version=version,
        compression=compression, use_dictionary=False, use_byte_stream_split=True,
        write_statistics=False, write_page_checksum=False, row_group_size=count,
    )
    data = sink.getvalue().to_pybytes()
    parquet = pq.ParquetFile(pa.BufferReader(data))
    readback = parquet.read(use_threads=False).column(0).chunk(0)
    assert readback.is_valid().to_pylist() == present
    raw = readback.buffers()[1].to_pybytes()
    assert [raw[i * width:(i + 1) * width] for i, flag in enumerate(present) if flag] == words
    assert parquet.metadata.num_row_groups == 1
    codec = footer_codec(data)
    assert codec == {"NONE": 0, "SNAPPY": 1}[compression]
    leaf = parquet.schema.column(0)
    assert leaf.physical_type == physical and leaf.max_definition_level == 1
    assert leaf.max_repetition_level == 0
    declared = "-"
    if physical == "FIXED_LEN_BYTE_ARRAY":
        declared = leaf.length
        assert declared == width
    column = parquet.metadata.row_group(0).column(0)
    assert not column.has_dictionary_page
    offset = column.data_page_offset
    transport = TMemoryBuffer(data[offset:offset + column.total_compressed_size])
    header = header_fields(TCompactProtocol(transport), (5, 8))
    header_length = transport.cstringio_buf.tell()
    decoded, compressed = header[2], header[3]
    assert header_length + compressed == column.total_compressed_size
    assert header_length + decoded == column.total_uncompressed_size
    body = transport.readAll(compressed)
    if version == "1.0":
        h = header[5]
        assert header[1] == 0 and h[1] == count and h[2] == 9 and h[3] == h[4] == 3
        assert codec == 0 and decoded == compressed
        level_bytes = struct.unpack_from("<I", body)[0]
        assert 4 + level_bytes <= len(body)
        lanes = body[4 + level_bytes:]
        flag = "-"
    else:
        h = header[8]
        assert header[1] == 3 and h[1] == h[3] == count and h[2] == nulls
        assert h[4] == 9 and h[6] == 0
        level_bytes, is_compressed = h[5], h[7]
        assert 0 <= level_bytes <= min(decoded, compressed)
        flag = int(is_compressed)
        lanes = body[level_bytes:]
        if codec == 0:
            assert not is_compressed and decoded == compressed
        else:
            assert is_compressed and compressed < decoded
            lanes = pa.decompress(lanes, decoded - level_bytes, codec="snappy").to_pybytes()
    assert lanes == b"".join(bytes(word[i] for word in words) for i in range(width))
    print(version, name, physical, declared, codec, compressed, decoded, count, nulls,
          level_bytes, flag, body.hex(), sep="\t")


def pack(form, values):
    return [struct.pack(form, value) for value in values]


if __name__ == "__main__":
    assert pa.__version__ == "26.0.1"
    mixed = [True, False, True, True, False, True]
    int32_words = pack("<i", [-(2**31), -2, 0x01020304, 2**31 - 1])
    for version in ("1.0", "2.0"):
        emit(version, "signed32", "INT32", pa.int32(), 4, int32_words, mixed)
        emit(version, "signed64", "INT64", pa.int64(), 8,
             pack("<q", [-(2**63), -2, 0x0102030405060708, 2**63 - 1]), mixed)
        emit(version, "float-bits", "FLOAT", pa.float32(), 4,
             pack("<I", [0x7FC12345, 0xFFC54321, 0x80000000, 1]), mixed)
        emit(version, "double-bits", "DOUBLE", pa.float64(), 8,
             pack("<Q", [0x7FF8123456789ABC, 0xFFF8ABCDEF012345, 0x8000000000000000, 1]), mixed)
        emit(version, "fixed", "FIXED_LEN_BYTE_ARRAY", pa.binary(3), 3,
             [bytes.fromhex(s) for s in ("00ff41", "80007f", "112233")], [True, False, True, False, True])
        emit(version, "all-null", "FIXED_LEN_BYTE_ARRAY", pa.binary(3), 3, [], [False, False, False])
    emit("2.0", "signed32-snappy", "INT32", pa.int32(), 4, int32_words * 16, mixed * 16, "SNAPPY")
