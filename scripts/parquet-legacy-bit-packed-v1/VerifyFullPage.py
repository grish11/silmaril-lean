"""Check the unchanged page extent, metadata, and observed PyArrow readback."""

from pathlib import Path
import struct
import sys

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

EXPECTED = [17, None, -9, 300, None, None, 0, None, -(2**31)]


def field_numbers(protocol, nested_ids=()):
    result = {}
    protocol.readStructBegin()
    while True:
        _, kind, field = protocol.readFieldBegin()
        if kind == TType.STOP:
            break
        if kind == TType.I32:
            result[field] = protocol.readI32()
        elif kind == TType.STRUCT and field in nested_ids:
            result[field] = field_numbers(protocol)
        else:
            protocol.skip(kind)
        protocol.readFieldEnd()
    protocol.readStructEnd()
    return result


def verify(path):
    data = path.read_bytes()
    file = pq.ParquetFile(pa.BufferReader(data))
    assert file.metadata.num_row_groups == 1
    assert file.metadata.created_by.startswith("parquet-mr version 1.16.0")
    values = file.read(use_threads=False).column(0)
    assert values.type == pa.int32()
    arrow_readback = [None, 17, None, None, -9, 300, None, 0, None]
    assert values.to_pylist() == arrow_readback
    schema = file.schema.column(0)
    assert schema.physical_type == "INT32" and schema.max_repetition_level == 0
    assert schema.max_definition_level == 1
    column = file.metadata.row_group(0).column(0)
    assert column.compression == "UNCOMPRESSED" and column.num_values == len(EXPECTED)
    assert not column.has_dictionary_page
    start = column.data_page_offset
    end = start + column.total_compressed_size
    transport = TMemoryBuffer(data[start:end])
    header = field_numbers(TCompactProtocol(transport), (5,))
    header_size = transport.cstringio_buf.tell()
    assert header[1] == 0 and header[5] == {1: 9, 2: 0, 3: 4, 4: 3}
    assert 4 not in header and header[2] == header[3] == 22
    assert header_size + header[3] == column.total_compressed_size == column.total_uncompressed_size
    body = transport.readAll(header[3])

    level_bytes = (len(EXPECTED) + 7) // 8
    assert body[:level_bytes] == bytes.fromhex("b280")
    assert [bool(body[i // 8] & (0x80 >> (i % 8))) for i in range(len(EXPECTED))] == [
        value is not None for value in EXPECTED
    ]
    suffix = body[level_bytes:]
    plain = [x for x, in struct.iter_unpack("<i", suffix)]
    assert plain == [x for x in EXPECTED if x is not None]
    plain_values = iter(plain)
    assert [next(plain_values) if (body[i // 8] >> (i % 8)) & 1 else None
            for i in range(len(EXPECTED))] == arrow_readback
    print("created_by", file.metadata.created_by, sep="\t")
    print("frame", start, start + header_size, end, sep="\t")
    print("header_hex", data[start:start + header_size].hex(), sep="\t")
    print("body_hex", body.hex(), sep="\t")
    print("definition_hex", body[:level_bytes].hex(), sep="\t")
    print("plain_suffix_hex", suffix.hex(), sep="\t")
    print("pyarrow_26_0_1_readback", arrow_readback, sep="\t")


if __name__ == "__main__":
    assert pa.__version__ == "26.0.1"
    verify(Path(sys.argv[1]))
