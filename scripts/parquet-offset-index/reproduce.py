"""Generate pinned Arrow fixtures and verify raw OffsetIndex using Apache Thrift."""

from hashlib import sha256
from pathlib import Path
import struct
import sys

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer


def read_fields(protocol, shape):
    types = {TType.I32: protocol.readI32, TType.I64: protocol.readI64}

    def read_value(kind, nested):
        if kind == TType.STRUCT:
            return read_fields(protocol, nested)
        if kind == TType.LIST:
            element_kind, size = protocol.readListBegin()
            assert element_kind == TType.STRUCT
            values = [read_fields(protocol, nested) for _ in range(size)]
            protocol.readListEnd()
            return values
        return types[kind]()

    values = {}
    protocol.readStructBegin()
    while True:
        _, kind, field = protocol.readFieldBegin()
        if kind == TType.STOP:
            break
        if field in shape:
            expected, nested = shape[field]
            assert kind == expected and field not in values
            values[field] = read_value(kind, nested)
        else:
            protocol.skip(kind)
        protocol.readFieldEnd()
    protocol.readStructEnd()
    return values


class BinarySkippingCompactProtocol(TCompactProtocol):
    # The Thrift generic skip path calls readString for both UTF-8 and opaque bytes.
    def readString(self):
        return self.readBinary()


def parse(data, shape):
    transport = TMemoryBuffer(data)
    return read_fields(BinarySkippingCompactProtocol(transport), shape), transport.cstringio_buf.tell()


I32 = (TType.I32, None)
I64 = (TType.I64, None)
COLUMN = {4: I64, 5: I32}
ROW_GROUP = {1: (TType.LIST, COLUMN), 3: I64}
FOOTER = {4: (TType.LIST, ROW_GROUP)}
OFFSET_INDEX = {1: (TType.LIST, {1: I64, 2: I32, 3: I64})}
PAGE = {
    1: I32,
    3: I32,
    4: I32,
    5: (TType.STRUCT, {1: I32, 2: I32}),
    8: (TType.STRUCT, {1: I32, 3: I32, 4: I32}),
}
VALUES = [None if i % 5 == 0 else 3 * i - 19 for i in range(24)]


def check(path, page_version, indexed):
    parquet = pq.ParquetFile(path)
    assert parquet.read().column(0).to_pylist() == VALUES
    leaf = parquet.schema.column(0)
    assert leaf.physical_type == "INT32"
    assert (leaf.max_repetition_level, leaf.max_definition_level) == (0, 1)
    data = path.read_bytes()
    assert data[:4] == data[-4:] == b"PAR1"
    footer_start = len(data) - 8 - struct.unpack("<I", data[-8:-4])[0]
    footer, consumed = parse(data[footer_start:-8], FOOTER)
    assert consumed == len(data) - 8 - footer_start
    assert len(footer[4]) == 2
    print(path.name, sha256(data).hexdigest())
    for group_number, group in enumerate(footer[4]):
        [column] = group[1]
        chunk = parquet.metadata.row_group(group_number).column(0)
        assert chunk.has_offset_index == indexed and not chunk.has_dictionary_page
        assert chunk.compression == ("UNCOMPRESSED" if page_version == "1.0" else "SNAPPY")
        if not indexed:
            assert not column
            continue
        start, length = column[4], column[5]
        assert chunk.data_page_offset + chunk.total_compressed_size <= start < start + length <= footer_start
        index, consumed = parse(data[start:start + length], OFFSET_INDEX)
        assert consumed == length
        locations = index[1]
        assert len(locations) == 3
        offset = chunk.data_page_offset
        first_row = 0
        for location in locations:
            assert (location[1], location[3]) == (offset, first_row)
            size = location[2]
            header, header_size = parse(data[offset:offset + size], PAGE)
            assert header_size + header[3] == size
            if page_version == "1.0":
                assert header[1] == 0 and set(header) == {1, 3, 5}
                assert header[5][2] == 0
                first_row += header[5][1]
            else:
                assert header[1] == 3 and set(header) == {1, 3, 8}
                assert header[8][1] == header[8][3] and header[8][4] == 0
                first_row += header[8][3]
            offset += size
        assert first_row == group[3] == 12
        assert offset == chunk.data_page_offset + chunk.total_compressed_size
        print(f"  row group {group_number}, index [{start}, {start + length}), "
              f"(offset, size, first row) = {[tuple(item[i] for i in (1, 2, 3)) for item in locations]}")


def main(destination):
    assert pa.__version__ == "26.0.1"
    destination.mkdir(parents=True, exist_ok=True)
    table = pa.table({"number": pa.array(VALUES, type=pa.int32())})
    for name, page_version, compression, indexed in (
        ("v1-index.parquet", "1.0", "NONE", True),
        ("v2-index.parquet", "2.0", "SNAPPY", True),
        ("v1-no-index.parquet", "1.0", "NONE", False),
    ):
        path = destination / name
        pq.write_table(table, path, data_page_version=page_version, compression=compression,
                       use_dictionary=False, write_page_index=indexed, row_group_size=12,
                       write_batch_size=4, max_rows_per_page=4)
        check(path, page_version, indexed)


if __name__ == "__main__":
    main(Path(sys.argv[1]))
