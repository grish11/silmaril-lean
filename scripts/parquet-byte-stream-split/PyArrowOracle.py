"""Extract exact BYTE_STREAM_SPLIT data pages from PyArrow 26.0.1."""

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


def emit(name, physical_type, dtype, width, words):
    count = len(words) // width
    schema = pa.schema([pa.field("v", dtype, nullable=False)])
    array = pa.Array.from_buffers(dtype, count, [None, pa.py_buffer(words)])
    sink = pa.BufferOutputStream()
    pq.write_table(
        pa.Table.from_arrays([array], schema=schema), sink, version="2.6", data_page_version="1.0",
        compression="NONE", use_dictionary=False, use_byte_stream_split=True, write_statistics=False,
        write_page_checksum=False, row_group_size=count,
    )
    data = sink.getvalue().to_pybytes()
    parquet = pq.ParquetFile(pa.BufferReader(data))
    readback = parquet.read(use_threads=False).column(0).chunk(0)
    assert len(readback) == count and readback.null_count == 0
    assert readback.buffers()[1].to_pybytes() == words
    assert parquet.metadata.num_row_groups == 1 and footer_codec(data) == 0
    leaf = parquet.schema.column(0)
    assert leaf.physical_type == physical_type
    assert leaf.max_definition_level == leaf.max_repetition_level == 0
    if physical_type == "FIXED_LEN_BYTE_ARRAY":
        assert leaf.length == width
    column = parquet.metadata.row_group(0).column(0)
    assert not column.has_dictionary_page
    offset = column.data_page_offset
    transport = TMemoryBuffer(data[offset:offset + column.total_compressed_size])
    header = header_fields(TCompactProtocol(transport), (5,))
    header_length = transport.cstringio_buf.tell()
    assert header[1] == 0 and header[5][1] == count and header[5][2] == 9
    assert header[2] == header[3] == count * width
    assert header_length + header[3] == column.total_compressed_size == column.total_uncompressed_size
    lanes = transport.readAll(header[3])
    assert lanes == b"".join(words[lane::width] for lane in range(width))
    print(name, count, width, lanes.hex(), sep="\t")


if __name__ == "__main__":
    assert pa.__version__ == "26.0.1"
    emit("INT32", "INT32", pa.int32(), 4, struct.pack("<4i", -(2**31), -2, 0x01020304, 2**31 - 1))
    emit("INT64", "INT64", pa.int64(), 8, struct.pack("<4q", -(2**63), -2, 0x0102030405060708, 2**63 - 1))
    emit("FLOAT", "FLOAT", pa.float32(), 4, struct.pack("<4I", 0x80000000, 0x3FA00000, 0xFF800000, 0x7FC00000))
    emit("DOUBLE", "DOUBLE", pa.float64(), 8,
         struct.pack("<4Q", 0x8000000000000000, 0x3FF4000000000000, 0xFFF0000000000000, 0x7FF8000000000000))
    emit("FIXED_LEN_BYTE_ARRAY", "FIXED_LEN_BYTE_ARRAY", pa.binary(3), 3, bytes.fromhex("00ff4180007f112233"))
    emit("FLOAT_NAN_PAYLOAD", "FLOAT", pa.float32(), 4, struct.pack("<3I", 0x7FC12345, 0xFFC54321, 1))
    emit("DOUBLE_NAN_PAYLOAD", "DOUBLE", pa.float64(), 8,
         struct.pack("<3Q", 0x7FF8123456789ABC, 0xFFF8ABCDEF012345, 1))
