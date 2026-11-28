"""Reproduce exact FIXED_LEN_BYTE_ARRAY encoding-7 pages from PyArrow."""

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

MIXED = [b"\xff\x00a", None, b"\xff\x00b", b"\xff\x00b"]
REQUIRED = [bytes.fromhex(word) for word in ("00ff010203", "00ff010204", "00ff010204", "7f80000100")]
ALL_NULL = [None] * 3


def emit(version, name, width, values, nullable):
    dtype = pa.binary(width)
    schema = pa.schema([pa.field("v", dtype, nullable=nullable)])
    table = pa.Table.from_arrays([pa.array(values, type=dtype)], schema=schema)
    sink = pa.BufferOutputStream()
    pq.write_table(
        table, sink, version="2.6", data_page_version=version, compression="NONE",
        use_dictionary=False, column_encoding="DELTA_BYTE_ARRAY", write_statistics=False,
        write_page_checksum=False, row_group_size=len(values),
    )
    data = sink.getvalue().to_pybytes()
    parquet = pq.ParquetFile(pa.BufferReader(data))
    readback = parquet.read(use_threads=False).column(0)
    assert readback.type == dtype and readback.to_pylist() == values
    assert parquet.metadata.num_row_groups == 1 and footer_codec(data) == 0
    leaf = parquet.schema.column(0)
    assert leaf.physical_type == "FIXED_LEN_BYTE_ARRAY" and leaf.length == width
    assert leaf.max_definition_level == int(nullable) and leaf.max_repetition_level == 0
    column = parquet.metadata.row_group(0).column(0)
    assert not column.has_dictionary_page
    start = column.data_page_offset
    transport = TMemoryBuffer(data[start:start + column.total_compressed_size])
    header = header_fields(TCompactProtocol(transport), (5, 8))
    header_size = transport.cstringio_buf.tell()
    size = header[2]
    assert size == header[3] and 4 not in header
    assert header_size + size == column.total_compressed_size == column.total_uncompressed_size
    body = transport.readAll(size)
    count = len(values)
    nulls = values.count(None)
    if version == "1.0":
        h = header[5]
        assert header[1] == 0 and h[1] == count and h[2] == 7 and h[3] == h[4] == 3
        levels = struct.unpack_from("<I", body)[0] if nullable else 0
        scalar_offset = 4 + levels if nullable else 0
    else:
        h = header[8]
        assert header[1] == 3 and h[1] == h[3] == count and h[2] == nulls
        assert h[4] == 7 and h[6] == 0 and h[7] is False
        levels = scalar_offset = h[5]
    assert scalar_offset < len(body)
    scalars = body[scalar_offset:]
    print(version, name, leaf.length, int(nullable), count, nulls, levels, body.hex(), scalars.hex(), sep="\t")


if __name__ == "__main__":
    assert pa.__version__ == "26.0.1"
    for version in ("1.0", "2.0"):
        emit(version, "mixed", 3, MIXED, True)
        emit(version, "required", 5, REQUIRED, False)
        emit(version, "all-null", 3, ALL_NULL, True)
