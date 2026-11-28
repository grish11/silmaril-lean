"""Extract checked flat V1/V2 delta pages from PyArrow 26.0.1."""

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


def emit(version, name, physical, dtype, encoding, encoding_id, values):
    schema = pa.schema([pa.field("v", dtype, nullable=True)])
    table = pa.Table.from_arrays([pa.array(values, type=dtype)], schema=schema)
    sink = pa.BufferOutputStream()
    pq.write_table(
        table, sink, version="2.6", data_page_version=version, compression="NONE",
        use_dictionary=False, column_encoding=encoding, write_statistics=False,
        write_page_checksum=False, row_group_size=len(values),
    )
    data = sink.getvalue().to_pybytes()
    parquet = pq.ParquetFile(pa.BufferReader(data))
    assert parquet.read(use_threads=False).column(0).to_pylist() == values
    assert parquet.metadata.num_row_groups == 1 and footer_codec(data) == 0
    leaf = parquet.schema.column(0)
    assert leaf.physical_type == physical
    assert leaf.max_definition_level == 1 and leaf.max_repetition_level == 0
    column = parquet.metadata.row_group(0).column(0)
    assert not column.has_dictionary_page
    offset = column.data_page_offset
    transport = TMemoryBuffer(data[offset:offset + column.total_compressed_size])
    header = header_fields(TCompactProtocol(transport), (5, 8))
    header_length = transport.cstringio_buf.tell()
    assert header[2] == header[3]
    assert header_length + header[3] == column.total_compressed_size == column.total_uncompressed_size
    body = transport.readAll(header[3])
    nulls = values.count(None)
    if version == "1.0":
        h = header[5]
        assert header[1] == 0 and h[1] == len(values) and h[2] == encoding_id and h[3] == h[4] == 3
        level_bytes = struct.unpack_from("<I", body)[0]
        scalar_offset = 4 + level_bytes
    else:
        h = header[8]
        assert header[1] == 3 and h[1] == h[3] == len(values) and h[2] == nulls
        assert h[4] == encoding_id and h[6] == 0 and h[7] is False
        level_bytes = h[5]
        scalar_offset = level_bytes
    assert 0 <= scalar_offset <= len(body)
    scalars = body[scalar_offset:]
    print(version, name, physical, encoding_id, len(values), nulls, level_bytes, body.hex(),
          scalars.hex() or "-", sep="\t")


if __name__ == "__main__":
    assert pa.__version__ == "26.0.1"
    for version in ("1.0", "2.0"):
        emit(version, "signed32", "INT32", pa.int32(), "DELTA_BINARY_PACKED", 5,
             [19, None, -4, 19, None, 7, -4])
        emit(version, "signed64", "INT64", pa.int64(), "DELTA_BINARY_PACKED", 5,
             [5000000000, None, 4999999997, None, 4999999994])
        emit(version, "length", "BYTE_ARRAY", pa.binary(), "DELTA_LENGTH_BYTE_ARRAY", 6,
             [b"", None, b"\xc3\xa9", b"\xff\x00\x80", None, b"xy"])
        emit(version, "prefix", "BYTE_ARRAY", pa.binary(), "DELTA_BYTE_ARRAY", 7,
             [b"axis", None, b"axle", b"\xff\x00\x80", None, b"\xff\x00\x81", b"", b""])
        emit(version, "all-null", "BYTE_ARRAY", pa.binary(), "DELTA_BYTE_ARRAY", 7,
             [None, None, None])
