"""Reproduce Snappy V1/V2 fixtures and verify their codec-covered slices."""

import argparse
from hashlib import sha256
from pathlib import Path
import struct

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

assert pa.__version__ == "26.0.1"
SCHEMA = pa.schema(
    [pa.field("required_i32", pa.int32(), nullable=False), pa.field("optional_i32", pa.int32())]
)
PAGE_ROWS = 16
GROUP_ROWS = 2 * PAGE_ROWS
TOTAL_ROWS = 3 * GROUP_ROWS
VALUES = [
    [-(i // PAGE_ROWS) for i in range(TOTAL_ROWS)],
    [None if i % 4 == 1 else
     (300 if i // GROUP_ROWS == 1 else ((i * 1640531527 + 13011) % 2**32) - 2**31)
     for i in range(TOTAL_ROWS)],
]
TABLE = pa.Table.from_arrays([pa.array(column, type=pa.int32()) for column in VALUES], schema=SCHEMA)
SNAPPY = pa.Codec("snappy")


def fields(protocol, nested=()):
    result = {}
    protocol.readStructBegin()
    while True:
        _, tag, key = protocol.readFieldBegin()
        if tag == TType.STOP:
            break
        if tag == TType.I32:
            result[key] = protocol.readI32()
        elif tag == TType.BOOL:
            result[key] = protocol.readBool()
        elif tag == TType.STRUCT and key in nested:
            result[key] = fields(protocol)
        else:
            protocol.skip(tag)
        protocol.readFieldEnd()
    protocol.readStructEnd()
    return result


def verify(path, version):
    raw = path.read_bytes()
    parquet = pq.ParquetFile(path)
    assert parquet.read().equals(TABLE)
    assert parquet.metadata.num_row_groups == 3
    footer = len(raw) - 8 - int.from_bytes(raw[-8:-4], "little")
    damage = None
    flags = set()
    print(path.name, sha256(raw).hexdigest(), "footer", footer)
    for g in range(3):
        group = parquet.metadata.row_group(g)
        assert group.num_rows == GROUP_ROWS and group.num_columns == 2
        for c in range(2):
            column = group.column(c)
            assert column.compression == "SNAPPY" and not column.has_dictionary_page
            assert column.num_values == group.num_rows
            cursor = column.data_page_offset
            stop = cursor + column.total_compressed_size
            assert 4 <= cursor < stop <= footer
            for p in range(2):
                transport = TMemoryBuffer(raw[cursor:stop])
                header = fields(TCompactProtocol(transport), (5, 8))
                start = cursor + transport.cstringio_buf.tell()
                end = start + header[3]
                assert cursor < start < end <= stop and 4 not in header
                base = GROUP_ROWS * g + PAGE_ROWS * p
                expected = [i for i in VALUES[c][base:base + PAGE_ROWS] if i is not None]
                if version == "1.0":
                    assert header[1] == 0
                    data = header[5]
                    assert [data[k] for k in (1, 2, 3, 4)] == [PAGE_ROWS, 0, 3, 3]
                    flag = True
                    encoded = start
                    target = header[2]
                    plain = SNAPPY.decompress(raw[encoded:end], target).to_pybytes()
                    levels = 0 if c == 0 else 4 + int.from_bytes(plain[:4], "little")
                    plain = plain[levels:]
                else:
                    assert header[1] == 3
                    data = header[8]
                    assert [data[k] for k in (1, 2, 3, 4, 6)] == [PAGE_ROWS, c * (PAGE_ROWS // 4), PAGE_ROWS, 0, 0]
                    flag = data.get(7, True)
                    levels = data[5]
                    target = header[2] - levels
                    encoded = start + levels
                    if flag:
                        plain = SNAPPY.decompress(raw[encoded:end], target).to_pybytes()
                    else:
                        assert end - encoded == target
                        plain = raw[encoded:end]
                flags.add(flag)
                assert 0 <= levels and encoded < end and target < 127
                assert list(struct.iter_unpack("<i", plain)) == [(i,) for i in expected]
                if flag:
                    assert raw[encoded] == target
                if (g, c, p) == (1, 1, 1):
                    assert flag
                    damage = (cursor, encoded, target)
                print(g, c, p, "header", cursor, "body", start, end,
                      "valueExtent", encoded, end, "decoded", target, "levelBytes", levels, "snappy", flag)
                cursor = end
            assert cursor == stop
    assert flags == ({True} if version == "1.0" else {True, False})
    return raw, damage


def damaged_file(path, raw, damage):
    header, offset, target = damage
    changed = bytearray(raw)
    changed[offset] = target + 1
    path.write_bytes(changed)
    parquet = pq.ParquetFile(path)
    assert parquet.read_row_group(0).equals(TABLE.slice(0, GROUP_ROWS))
    try:
        parquet.read_row_group(1)
    except (OSError, pa.ArrowInvalid) as error:
        assert 'Output buffer size' in str(error)
        print(path.name, sha256(changed).hexdigest(), "rejected group 1 column 1 page 1",
              "header", header, "byte", offset, "length", target, "changed to", target + 1)
    else:
        raise AssertionError("accepted overdeclared Snappy result size")
    assert parquet.read_row_group(2).equals(TABLE.slice(2 * GROUP_ROWS, GROUP_ROWS))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    args = parser.parse_args()
    args.directory.mkdir(parents=True, exist_ok=True)
    for version in ("1.0", "2.0"):
        file = args.directory / f"snappy-plain-v{version[0]}.parquet"
        pq.write_table(
            TABLE, file, version="2.6", data_page_version=version, compression="snappy",
            use_dictionary=False, row_group_size=GROUP_ROWS, write_batch_size=PAGE_ROWS, data_page_size=1,
            write_statistics=False, write_page_checksum=False,
        )
        raw, mutation = verify(file, version)
        damaged_file(args.directory / f"snappy-plain-v{version[0]}-bad-size.parquet", raw, mutation)


if __name__ == "__main__":
    main()
