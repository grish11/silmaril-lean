"""Build a bounded zero-row Parquet fixture with one real V2 page header."""

from functools import partial
from hashlib import sha256
from struct import pack

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer


def record(writer, fields):
    writer.writeStructBegin("")
    for key, kind, emit in fields:
        writer.writeFieldBegin("", kind, key)
        emit()
        writer.writeFieldEnd()
    writer.writeFieldStop()
    writer.writeStructEnd()


def vector(writer, kind, values):
    writer.writeListBegin(kind, len(values))
    for emit in values:
        emit()
    writer.writeListEnd()


def empty_v2_header():
    page = TMemoryBuffer()
    writer = TCompactProtocol(page)

    def i32(key, value):
        return key, TType.I32, partial(writer.writeI32, value)

    def detail():
        no_compression = (7, TType.BOOL, partial(writer.writeBool, False))
        record(writer, [i32(key, 0) for key in range(1, 7)] + [no_compression])

    record(writer, [i32(1, 3), i32(2, 0), i32(3, 0), (8, TType.STRUCT, detail)])
    return page.getvalue()


def v2_empty_group():
    page = empty_v2_header()
    footer = TMemoryBuffer()
    writer = TCompactProtocol(footer)

    def i32(key, value):
        return key, TType.I32, partial(writer.writeI32, value)

    def i64(key, value):
        return key, TType.I64, partial(writer.writeI64, value)

    def text(key, value):
        return key, TType.STRING, partial(writer.writeString, value)

    def repeated(key, kind, values):
        return key, TType.LIST, partial(vector, writer, kind, values)

    def root():
        record(writer, [text(4, "schema"), i32(5, 1)])

    def leaf():
        record(writer, [i32(1, 6), i32(3, 1), text(4, "blob")])

    def column_metadata():
        record(writer, [
            i32(1, 6),
            repeated(2, TType.I32, [partial(writer.writeI32, tag) for tag in (0, 3)]),
            repeated(3, TType.STRING, [partial(writer.writeString, "blob")]),
            i32(4, 0), i64(5, 0), i64(6, len(page)), i64(7, len(page)), i64(9, 4),
        ])

    def chunk():
        record(writer, [i64(2, 4), (3, TType.STRUCT, column_metadata)])

    def group():
        record(writer, [repeated(1, TType.STRUCT, [chunk]), i64(2, len(page)), i64(3, 0)])

    record(writer, [
        i32(1, 2), repeated(2, TType.STRUCT, [root, leaf]), i64(3, 0),
        repeated(4, TType.STRUCT, [group]),
    ])
    footer = footer.getvalue()
    return b"PAR1" + page + footer + pack("<I", len(footer)) + b"PAR1"


def write_zero_cases(out):
    schema = pa.schema([pa.field("row_id", pa.int32(), nullable=False), pa.field("blob", pa.binary())])
    options = dict(version="2.6", data_page_version="2.0", compression="NONE", use_dictionary=False,
                   column_encoding="PLAIN", write_statistics=False, write_page_checksum=False,
                   store_schema=False)
    for case in ("schema-only", "zero-row-group"):
        path = out / f"{case}.parquet"
        with pq.ParquetWriter(path, schema, **options) as writer:
            if case == "zero-row-group":
                writer.write_table(schema.empty_table())
        with pq.ParquetFile(path) as source:
            groups = [(source.metadata.row_group(i).num_rows,
                       source.metadata.row_group(i).column(1).data_page_offset)
                      for i in range(source.num_row_groups)]
            assert source.schema_arrow == schema and source.read().num_rows == 0
            assert groups == ([] if case == "schema-only" else [(0, 0)])
        print(sha256(path.read_bytes()).hexdigest(), path.name, groups)

    data = v2_empty_group()
    with pq.ParquetFile(pa.BufferReader(data)) as source:
        assert source.schema_arrow == pa.schema([pa.field("blob", pa.binary())])
        assert source.num_row_groups == 1 and source.metadata.row_group(0).column(0).data_page_offset == 4
        assert source.read_row_group(0).num_rows == 0
    destination = out / "framed-zero-row-group.parquet"
    destination.write_bytes(data)
    print(sha256(data).hexdigest(), destination.name)
