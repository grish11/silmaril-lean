"""Extract exact PLAIN V1/V2 bodies from files written by PyArrow 26.0.1."""

from pathlib import Path
from runpy import run_path
import struct

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

footer_codec = run_path(
    str(Path(__file__).resolve().parents[1] / "parquet-payload-oracle" / "check.py")
)["footer_codec"]

MIXED = [7, None, -4, None, 19]
ALL_NULL = [None, None, None]


def header_fields(protocol, nested_ids=()):
    """Extract the integer fields and optional compression flag in concrete fixtures."""
    values = {}
    protocol.readStructBegin()
    while True:
        _, tag, field = protocol.readFieldBegin()
        if tag == TType.STOP:
            break
        if tag == TType.I32:
            values[field] = protocol.readI32()
        elif tag == TType.BOOL:
            values[field] = protocol.readBool()
        elif tag == TType.STRUCT and field in nested_ids:
            values[field] = header_fields(protocol)
        else:
            protocol.skip(tag)
        protocol.readFieldEnd()
    protocol.readStructEnd()
    return values


def emit(version, compression, name, values):
    schema = pa.schema([pa.field("v", pa.int32(), nullable=True)])
    table = pa.Table.from_arrays([pa.array(values, type=pa.int32())], schema=schema)
    sink = pa.BufferOutputStream()
    pq.write_table(
        table, sink, version="2.6", data_page_version=version, compression=compression,
        use_dictionary=False, column_encoding="PLAIN", write_statistics=False,
        write_page_checksum=False, row_group_size=len(values),
    )
    data = sink.getvalue().to_pybytes()
    parquet = pq.ParquetFile(pa.BufferReader(data))
    assert parquet.read().column(0).to_pylist() == values
    assert parquet.metadata.num_row_groups == 1
    leaf = parquet.schema.column(0)
    assert leaf.max_definition_level == 1 and leaf.max_repetition_level == 0
    column = parquet.metadata.row_group(0).column(0)
    assert not column.has_dictionary_page
    codec = footer_codec(data)
    assert codec == {"NONE": 0, "SNAPPY": 1}[compression]
    offset = column.data_page_offset
    transport = TMemoryBuffer(data[offset : offset + column.total_compressed_size])
    header = header_fields(TCompactProtocol(transport), (5, 8))
    decoded, compressed = header[2], header[3]
    header_length = transport.cstringio_buf.tell()
    assert header_length + compressed == column.total_compressed_size
    assert header_length + decoded == column.total_uncompressed_size
    body = transport.readAll(compressed)

    if version == "1.0":
        assert header[1] == 0
        inline = header[5]
        assert inline[1] == len(values) and inline[2] == 0
        assert inline[3] == inline[4] == 3
        fields = (len(values), "-", "-", "-", "-", "-")
        if codec == 0:
            prefix = 4 + struct.unpack_from("<I", body)[0]
            assert prefix <= len(body)
            assert [v for v, in struct.iter_unpack("<i", body[prefix:])] == [
                v for v in values if v is not None
            ]
    else:
        assert header[1] == 3
        inline = header[8]
        assert inline[1] == inline[3] == len(values)
        assert inline[2] == sum(v is None for v in values)
        assert inline[4] == 0 and inline[6] == 0
        flag = inline.get(7)
        fields = (
            inline[1], inline[2], inline[3], inline[6], inline[5],
            "-" if flag is None else int(flag),
        )
        assert 0 <= inline[5] <= min(decoded, compressed)
        if flag is False or codec == 0:
            assert [v for v, in struct.iter_unpack("<i", body[inline[5]:])] == [
                v for v in values if v is not None
            ]
    print(version, compression, name, codec, compressed, decoded, *fields, body.hex(), sep="\t")


if __name__ == "__main__":
    assert pa.__version__ == "26.0.1"
    for version in ("1.0", "2.0"):
        emit(version, "NONE", "mixed", MIXED)
        emit(version, "SNAPPY", "mixed", MIXED)
        emit(version, "SNAPPY", "all-null", ALL_NULL)
    emit("2.0", "SNAPPY", "mixed-compressed", MIXED * 16)
