"""Reproduce the fixture bytes with PyArrow 26.0.1 and Apache Thrift v0.25.0."""

import struct

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer


def header_fields(protocol, nested_ids=()):
    """Extract integer fields of the pinned PageHeader and its data headers."""
    fields = {}
    protocol.readStructBegin()
    while True:
        _, tag, field_id = protocol.readFieldBegin()
        if tag == TType.STOP:
            break
        if tag == TType.I32:
            fields[field_id] = protocol.readI32()
        elif tag == TType.STRUCT and field_id in nested_ids:
            fields[field_id] = header_fields(protocol)
        else:
            protocol.skip(tag)
        protocol.readFieldEnd()
    protocol.readStructEnd()
    return fields


def emit(version, name, optional, values):
    schema = pa.schema([pa.field("v", pa.int32(), nullable=optional)])
    table = pa.Table.from_arrays([pa.array(values, type=pa.int32())], schema=schema)
    output = pa.BufferOutputStream()
    pq.write_table(
        table,
        output,
        version="2.6",
        data_page_version=version,
        compression="NONE",
        use_dictionary=False,
        write_statistics=False,
        row_group_size=len(values),
    )
    container = output.getvalue()
    parquet = pq.ParquetFile(pa.BufferReader(container))
    assert parquet.read().column(0).to_pylist() == values
    assert parquet.metadata.num_row_groups == 1
    column = parquet.metadata.row_group(0).column(0)
    assert column.compression == "UNCOMPRESSED" and not column.has_dictionary_page
    raw = container.to_pybytes()
    offset = column.data_page_offset
    transport = TMemoryBuffer(raw[offset:])
    header = header_fields(TCompactProtocol(transport), (5, 8))
    header_size = transport.cstringio_buf.tell()
    assert header[2] == header[3]
    assert header_size + header[3] == column.total_compressed_size
    body = raw[offset + header_size : offset + header_size + header[3]]
    present = sum(value is not None for value in values)
    if version == "1.0":
        assert header[1] == 0   # DATA_PAGE
        data = header[5]
        assert data[1] == len(values) and data[2] == 0  # PLAIN
        if optional:
            assert data[3] == 3  # RLE definition levels
            declared = struct.unpack_from("<I", body)[0]
            level_end = 4 + declared
        else:
            declared = level_end = 0
    else:
        assert header[1] == 3   # DATA_PAGE_V2
        data = header[8]
        assert data[1] == data[3] == len(values)
        assert data[2] == len(values) - present
        assert data[4] == 0 and data[6] == 0  # PLAIN and zero repetition bytes
        declared = level_end = data[5]
    assert 0 <= level_end <= len(body)
    definitions, scalars = body[:level_end], body[level_end:]
    assert list(struct.iter_unpack("<i", scalars)) == [
        (value,) for value in values if value is not None
    ]
    print(
        version, name, len(values), present, declared,
        definitions.hex() or "-", scalars.hex() or "-", sep="\t",
    )


if __name__ == "__main__":
    assert pa.__version__ == "26.0.1"
    for page_version in ("1.0", "2.0"):
        emit(page_version, "required", False, [7, -4, 19])
        emit(page_version, "mixed-null", True, [7, None, -4, None, 19])
        emit(page_version, "all-null", True, [None, None, None])
