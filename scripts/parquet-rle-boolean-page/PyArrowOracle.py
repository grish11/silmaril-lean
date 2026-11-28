"""Reproduce flat RLE BOOLEAN page bodies written by pinned PyArrow."""

from pathlib import Path
from runpy import run_path
import struct

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

# In the repository this is the existing Thrift page-header reader used by
# the PLAIN oracle as well.
page_oracle = run_path(
    str(Path(__file__).resolve().parents[1] / "parquet-scalar-page" / "PyArrowOracle.py")
)
header_fields = page_oracle["header_fields"]
footer_codec = page_oracle["footer_codec"]

MIXED = [True, None, False, True, False, None, True]
REQUIRED = [True] * 16 + [False] * 16 + [True, False, True, False, True]
ALL_NULL = [None] * 3


def readback(data):
    return pq.ParquetFile(pa.BufferReader(data)).read(use_threads=False).column(0).to_pylist()


def check_bad_lengths(data, start, size):
    for lie in (size - 1, size + 1, 0xFFFFFFFF):
        mutant = data[:start] + struct.pack("<I", lie) + data[start + 4:]
        try:
            readback(mutant)
        except (pa.ArrowInvalid, OSError):
            continue
        raise AssertionError(f"RLE BOOLEAN scalar prefix {lie} was accepted")


def emit(version, name, values, nullable):
    schema = pa.schema([pa.field("v", pa.bool_(), nullable=nullable)])
    table = pa.Table.from_arrays([pa.array(values, type=pa.bool_())], schema=schema)
    sink = pa.BufferOutputStream()
    pq.write_table(
        table, sink, version="2.6", data_page_version=version, compression="NONE",
        use_dictionary=False, column_encoding="RLE", write_statistics=False,
        write_page_checksum=False, row_group_size=len(values),
    )
    data = sink.getvalue().to_pybytes()
    assert readback(data) == values
    parquet = pq.ParquetFile(pa.BufferReader(data))
    assert parquet.metadata.num_row_groups == 1 and footer_codec(data) == 0
    leaf = parquet.schema.column(0)
    assert leaf.physical_type == "BOOLEAN" and leaf.max_definition_level == int(nullable)
    assert leaf.max_repetition_level == 0
    column = parquet.metadata.row_group(0).column(0)
    assert not column.has_dictionary_page
    start = column.data_page_offset
    transport = TMemoryBuffer(data[start:start + column.total_compressed_size])
    header = header_fields(TCompactProtocol(transport), (5, 8))
    header_bytes = transport.cstringio_buf.tell()
    size = header[2]
    assert size == header[3]
    assert header_bytes + size == column.total_compressed_size == column.total_uncompressed_size
    body = transport.readAll(size)
    count = len(values)
    nulls = values.count(None)
    if version == "1.0":
        h = header[5]
        assert header[1] == 0 and h[1] == count and h[2] == h[3] == h[4] == 3
        levels = struct.unpack_from("<I", body)[0] if nullable else 0
        scalar_offset = 4 + levels if nullable else 0
    else:
        h = header[8]
        assert header[1] == 3 and h[1] == h[3] == count and h[2] == nulls
        assert h[4] == 3 and h[6] == 0 and h[7] is False
        levels = scalar_offset = h[5]
    payload_bytes = struct.unpack_from("<I", body, scalar_offset)[0]
    assert scalar_offset + 4 + payload_bytes == len(body)
    if name == "mixed":
        check_bad_lengths(data, start + header_bytes + scalar_offset, payload_bytes)
    if name == "all-null":
        assert payload_bytes == 0
    print(version, name, int(nullable), size, count, nulls, levels, body.hex(), sep="\t")


if __name__ == "__main__":
    assert pa.__version__ == "26.0.1"
    for version in ("1.0", "2.0"):
        emit(version, "mixed", MIXED, True)
        emit(version, "required", REQUIRED, False)
        emit(version, "all-null", ALL_NULL, True)
