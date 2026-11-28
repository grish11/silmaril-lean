"""Extract dictionary and data bodies from actual PyArrow 26.0.1 PLAIN dictionaries."""

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
MIXED = [19, None, -4, 19, None, 7, -4, 7, 19]
REPEATED = [None] + [-4] * 16 + [None]
ALL_NULL = [None, None, None]


def page_at(data, offset, stop, detail):
    transport = TMemoryBuffer(data[offset:stop])
    header = header_fields(TCompactProtocol(transport), (detail,))
    assert header[2] == header[3]
    header_length = transport.cstringio_buf.tell()
    body = transport.readAll(header[3])
    return header, body, offset + header_length + len(body)


def emit(version, name, values):
    schema = pa.schema([pa.field("v", pa.int32(), nullable=True)])
    table = pa.Table.from_arrays([pa.array(values, type=pa.int32())], schema=schema)
    sink = pa.BufferOutputStream()
    pq.write_table(
        table, sink, version="2.6", data_page_version=version, compression="NONE",
        use_dictionary=True, write_statistics=False, write_page_checksum=False,
        row_group_size=len(values),
    )
    data = sink.getvalue().to_pybytes()
    parquet = pq.ParquetFile(pa.BufferReader(data))
    assert parquet.read().column(0).to_pylist() == values
    assert parquet.metadata.num_row_groups == 1 and footer_codec(data) == 0
    leaf = parquet.schema.column(0)
    assert leaf.physical_type == "INT32"
    assert leaf.max_definition_level == 1 and leaf.max_repetition_level == 0
    column = parquet.metadata.row_group(0).column(0)
    assert column.has_dictionary_page
    start = column.dictionary_page_offset
    stop = start + column.total_compressed_size
    assert column.total_compressed_size == column.total_uncompressed_size
    dictionary, dictionary_body, next_offset = page_at(data, start, stop, 7)
    assert dictionary[1] == 2 and dictionary[7][2] == 0 and next_offset == column.data_page_offset
    entries = [v for v, in struct.iter_unpack("<i", dictionary_body)]
    assert entries == list(dict.fromkeys(v for v in values if v is not None))
    assert len(entries) == dictionary[7][1]

    nulls = values.count(None)
    if version == "1.0":
        header, body, next_offset = page_at(data, next_offset, stop, 5)
        h = header[5]
        assert header[1] == 0 and h[1] == len(values) and h[2] == 8 and h[3] == h[4] == 3
        level_bytes = struct.unpack_from("<I", body)[0]
        index_offset = 4 + level_bytes
        encoding = h[2]
    else:
        header, body, next_offset = page_at(data, next_offset, stop, 8)
        h = header[8]
        assert header[1] == 3 and h[1] == h[3] == len(values) and h[2] == nulls
        assert h[4] == 8 and h[6] == 0 and h[7] is False
        level_bytes = h[5]
        index_offset = level_bytes
        encoding = h[4]
    assert next_offset == stop and 0 <= index_offset <= len(body)
    indices = body[index_offset:]
    assert indices and indices[0] <= 32
    print(version, name, len(values), nulls, level_bytes, encoding, len(entries),
          dictionary_body.hex() or "-", body.hex(), indices.hex(), sep="\t")


if __name__ == "__main__":
    assert pa.__version__ == "26.0.1"
    for version in ("1.0", "2.0"):
        emit(version, "mixed", MIXED)
        emit(version, "repeat", REPEATED)
        emit(version, "all-null", ALL_NULL)
