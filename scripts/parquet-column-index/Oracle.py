"""Generate a pinned PyArrow file and verify the raw ColumnIndex with Thrift."""

from hashlib import sha256
from pathlib import Path
import struct
import sys

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer


class BinaryCompact(TCompactProtocol):
    def readString(self):
        # Generic skip treats Thrift BINARY and STRING as the same type.
        return self.readBinary()


def read_value(protocol, kind, detail):
    if kind == TType.STRUCT:
        return read_fields(protocol, detail)
    if kind == TType.LIST:
        expected, nested = detail
        element, count = protocol.readListBegin()
        assert element == expected
        result = [read_value(protocol, element, nested) for _ in range(count)]
        protocol.readListEnd()
        return result
    return {
        TType.BOOL: protocol.readBool,
        TType.STRING: protocol.readBinary,
        TType.I32: protocol.readI32,
        TType.I64: protocol.readI64,
    }[kind]()


def read_fields(protocol, schema):
    protocol.readStructBegin()
    fields = {}
    while True:
        _, kind, tag = protocol.readFieldBegin()
        if kind == TType.STOP:
            break
        if tag in schema:
            expected, detail = schema[tag]
            assert kind == expected and tag not in fields
            fields[tag] = read_value(protocol, kind, detail)
        else:
            protocol.skip(kind)
        protocol.readFieldEnd()
    protocol.readStructEnd()
    return fields


def parse(data, schema):
    transport = TMemoryBuffer(data)
    result = read_fields(BinaryCompact(transport), schema)
    return result, transport.cstringio_buf.tell()


I32 = (TType.I32, None)
I64 = (TType.I64, None)
BOOL = (TType.BOOL, None)
BINARY = (TType.STRING, None)


def record(fields):
    return (TType.STRUCT, fields)


def items(value):
    return (TType.LIST, value)


CHUNK = {4: I64, 5: I32, 6: I64, 7: I32}
GROUP = {1: items(record(CHUNK)), 3: I64}
SCHEMA = {1: I32, 6: I32, 10: record({})}
FOOTER = {
    2: items(record(SCHEMA)),
    4: items(record(GROUP)),
    7: items(record({1: record({})})),
}
OFFSET_INDEX = {1: items(record({1: I64, 2: I32, 3: I64}))}
COLUMN_INDEX = {1: items(BOOL), 2: items(BINARY), 3: items(BINARY), 4: I32, 5: items(I64)}
PAGE = {1: I32, 3: I32, 5: record({1: I32, 2: I32})}
FIXTURE_SHA256 = "1b5710ef7f7291983c2bae4b62a20b34574982268e32fbbea227912b878653a5"
MIN_I32 = -(1 << 31)
MAX_I32 = (1 << 31) - 1
ROWS = [
    [MIN_I32, None, -9, 3, None, None, None, None, 0, 7, None, MAX_I32],
    [5, None, 7, 12, None, None, None, None, MIN_I32, -18, None, 8],
    [None, -5, 0, None, 8, 12, None, 10, -18, None, 5, -1],
]
ORDERS = [("ASCENDING", 1), ("DESCENDING", 2), ("UNORDERED", 0)]


def write(path):
    values = pa.array([value for group in ROWS for value in group], type=pa.int32())
    pq.write_table(
        pa.table({"number": values}), path, data_page_version="1.0", compression="NONE",
        use_dictionary=False, write_page_index=True, write_statistics=True,
        row_group_size=12, write_batch_size=4, max_rows_per_page=4,
    )


def checked_span(source, footer_start, offset, length, schema):
    assert 4 <= offset < offset + length <= footer_start
    result, consumed = parse(source[offset:offset + length], schema)
    assert consumed == length
    return result


def check(path):
    source = path.read_bytes()
    assert sha256(source).hexdigest() == FIXTURE_SHA256
    parquet = pq.ParquetFile(path)
    assert parquet.num_row_groups == len(ROWS)
    footer_start = len(source) - 8 - struct.unpack("<I", source[-8:-4])[0]
    metadata, consumed = parse(source[footer_start:-8], FOOTER)
    assert consumed == len(source) - 8 - footer_start
    assert metadata[2] == [{}, {1: 1}] and metadata[7] == [{1: {}}]
    print(path.name, sha256(source).hexdigest())
    print("Footer declares TYPE_ORDER and a physical INT32 leaf with absent converted and logical tags.")

    for group, ((order_name, order), expected_rows) in enumerate(zip(ORDERS, ROWS, strict=True)):
        rows = parquet.read_row_group(group).column(0).to_pylist()
        assert rows == expected_rows
        [chunk] = metadata[4][group][1]
        code = checked_span(source, footer_start, chunk[6], chunk[7], COLUMN_INDEX)
        positions = checked_span(source, footer_start, chunk[4], chunk[5], OFFSET_INDEX)[1]
        assert code[4] == order and len(positions) == 3

        starts = [position[3] for position in positions] + [len(rows)]
        null_pages, mins, maxes, counts, bounds = [], [], [], [], []
        for position, first, stop in zip(positions, starts[:-1], starts[1:], strict=True):
            start, length = position[1], position[2]
            header, header_size = parse(source[start:start + length], PAGE)
            assert header[1] == 0 and header[5] == {1: stop - first, 2: 0}
            assert header_size + header[3] == length
            present = [value for value in rows[first:stop] if value is not None]
            null_pages.append(not present)
            mins.append(struct.pack("<i", min(present)) if present else b"")
            maxes.append(struct.pack("<i", max(present)) if present else b"")
            counts.append(stop - first - len(present))
            bounds.append((min(present), max(present)) if present else None)

        assert code[1] == null_pages and code[2] == mins and code[3] == maxes and code[5] == counts
        if order == 1:
            assert bounds[0][1] > bounds[2][0]
        if order == 2:
            assert bounds[2][1] > bounds[0][0]
        print(f"Group {group} {order_name}, ColumnIndex [{chunk[6]}, {chunk[6] + chunk[7]})")
        print(f"  signed bounds {bounds}, null counts {counts}")
        print(f"  wire lower {[value.hex() for value in mins]}, wire upper {[value.hex() for value in maxes]}")


    check_corruptions(source, footer_start)


def patch(source, *changes):
    result = bytearray(source)
    for offset, old, new in changes:
        assert result[offset] == old
        result[offset] = new
    return bytes(result)


def check_corruptions(source, footer_start):
    start, stop = 291, 338
    bad_flag = patch(source, (294, 1, 2))
    raw, consumed = parse(bad_flag[start:stop], COLUMN_INDEX)
    assert consumed == stop - start and not raw[1][1] and raw[2][1] == raw[3][1] == b""
    bad_count = patch(source, (327, 8, 6))
    raw, consumed = parse(bad_count[start:stop], COLUMN_INDEX)
    assert consumed == stop - start and raw[1][1] and raw[5][1] == 3
    bad_order = patch(source, (323, 2, 14))
    raw, consumed = parse(bad_order[start:stop], COLUMN_INDEX)
    assert consumed == stop - start and raw[4] == 7

    short_counts = source[start:325] + bytes([0x26, 8, 2, 0])
    raw, consumed = parse(short_counts, COLUMN_INDEX)
    assert consumed == len(short_counts) and len(raw[1]) == 3 and raw[5] == [4, 1]
    no_counts = source[start:324] + bytes([0])
    raw, consumed = parse(no_counts, COLUMN_INDEX)
    assert consumed == len(no_counts) and 5 not in raw

    bad_offset = patch(source, (443, 8, 10))
    raw, consumed = parse(bad_offset[440:464], OFFSET_INDEX)
    assert consumed == 24 and raw[1][0][1] == 5
    assert parse(source[4:39], PAGE) == parse(bad_offset[4:39], PAGE)
    extra_extent = patch(source, (641, 94, 96))
    metadata, _ = parse(extra_extent[footer_start:-8], FOOTER)
    [column] = metadata[4][0][1]
    assert (column[6], column[7]) == (start, stop - start + 1)
    _, used = parse(extra_extent[start:start + column[7]], COLUMN_INDEX)
    assert used == column[7] - 1

    print("Metadata controls from the pinned file")
    for name, content in (
        ("all-null flag mismatch", bad_flag),
        ("null-count mismatch", bad_count),
        ("unknown boundary tag", bad_order),
        ("short count list", short_counts),
        ("missing count list", no_counts),
        ("wrong paired page offset", bad_offset),
        ("surplus advertised byte", extra_extent),
    ):
        print(f"  {name}: {sha256(content).hexdigest()}")


if __name__ == "__main__":
    path = Path(sys.argv[1])
    assert pa.__version__ == "26.0.1"
    write(path)
    check(path)
