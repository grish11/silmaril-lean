"""Extract bounded PLAIN BYTE_ARRAY slices from actual PyArrow 26.0.1 pages."""

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
MIXED = [b"", None, bytes.fromhex("c3a9"), bytes.fromhex("ff0080"), None, b"xy"]
ALL_NULL = [None, None, None]


def emit(version, name, values):
    schema = pa.schema([pa.field("v", pa.binary(), nullable=True)])
    table = pa.Table.from_arrays([pa.array(values, type=pa.binary())], schema=schema)
    sink = pa.BufferOutputStream()
    pq.write_table(
        table, sink, version="2.6", data_page_version=version, compression="NONE",
        use_dictionary=False, column_encoding="PLAIN", write_statistics=False,
        write_page_checksum=False, row_group_size=len(values),
    )
    data = sink.getvalue().to_pybytes()
    parquet = pq.ParquetFile(pa.BufferReader(data))
    assert parquet.read().column(0).to_pylist() == values
    assert parquet.metadata.num_row_groups == 1 and footer_codec(data) == 0
    leaf = parquet.schema.column(0)
    assert leaf.physical_type == "BYTE_ARRAY" and leaf.logical_type.type == "NONE"
    assert leaf.max_definition_level == 1 and leaf.max_repetition_level == 0
    column = parquet.metadata.row_group(0).column(0)
    assert not column.has_dictionary_page
    offset = column.data_page_offset
    transport = TMemoryBuffer(data[offset : offset + column.total_compressed_size])
    header = header_fields(TCompactProtocol(transport), (5, 8))
    decoded, compressed = header[2], header[3]
    header_length = transport.cstringio_buf.tell()
    assert decoded == compressed
    assert header_length + compressed == column.total_compressed_size
    assert header_length + decoded == column.total_uncompressed_size
    body = transport.readAll(compressed)
    nulls = values.count(None)
    if version == "1.0":
        h = header[5]
        assert header[1] == 0 and h[1] == len(values) and h[2] == 0 and h[3] == h[4] == 3
        level_bytes = struct.unpack_from("<I", body)[0]
        scalar_offset = 4 + level_bytes
    else:
        h = header[8]
        assert header[1] == 3 and h[1] == h[3] == len(values) and h[2] == nulls
        assert h[4] == 0 and h[6] == 0 and h[7] is False
        level_bytes = h[5]
        scalar_offset = level_bytes
    assert 0 <= scalar_offset <= len(body)
    scalars = body[scalar_offset:]
    assert scalars == b"".join(struct.pack("<i", len(v)) + v for v in values if v is not None)
    print(version, name, len(values), nulls, level_bytes, body.hex(), scalars.hex() or "-", sep="\t")


if __name__ == "__main__":
    assert pa.__version__ == "26.0.1"
    for version in ("1.0", "2.0"):
        emit(version, "mixed", MIXED)
        emit(version, "all-null", ALL_NULL)
