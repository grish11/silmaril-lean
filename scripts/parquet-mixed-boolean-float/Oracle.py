"""Produce multi-group mixed nullable BOOLEAN/FLOAT Parquet and check its pages."""
from hashlib import sha256
from importlib.metadata import version as package_version
from pathlib import Path
from runpy import run_path
import struct
import sys

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

assert package_version("pyarrow") == "26.0.1"
assert package_version("thrift") == "0.25.0"
header_fields = run_path("scripts/parquet-scalar-page/PyArrowOracle.py")["header_fields"]
directory = Path(sys.argv[1])
directory.mkdir(parents=True, exist_ok=True)
boolean_base = ([True, None, False, False, True, True, None, False] * 2)
float_base = [
    0, None, 0x80000000, 0x7FC12345, 1, 0xFFC54321, 0x7F800000, None,
    0xFF800000, 0x3F800000, None, 0x80000001, 0x00800000, None, 0x7F7FFFFF, 0x80400000,
]
booleans = [
    value if value is None else value ^ (group == 1 or (group == 2 and index % 2 == 0))
    for group in range(3) for index, value in enumerate(boolean_base)
]
floats = [
    value if value is None else value ^ [0, 0x80000000, 1][group]
    for group in range(3) for value in float_base
]
schema = pa.schema([pa.field("enabled", pa.bool_()), pa.field("measurement", pa.float32())])
table = pa.Table.from_arrays(
    [pa.array(booleans, type=pa.bool_()), pa.array(floats, type=pa.uint32()).view(pa.float32())],
    schema=schema,
)


def verify_group(file, group):
    batch = file.read_row_group(group, use_threads=False)
    expected = slice(16 * group, 16 * group + 16)
    assert batch.column(0).to_pylist() == booleans[expected]
    assert batch.column(1).combine_chunks().view(pa.uint32()).to_pylist() == floats[expected]


def verify(path, version):
    source = path.read_bytes()
    file = pq.ParquetFile(path)
    assert file.metadata.num_row_groups == 3
    assert [file.schema.column(i).physical_type for i in range(2)] == ["BOOLEAN", "FLOAT"]
    assert all(file.schema.column(i).max_definition_level == 1 for i in range(2))
    assert all(file.schema.column(i).max_repetition_level == 0 for i in range(2))
    footer = len(source) - 8 - int.from_bytes(source[-8:-4], "little")
    print(path.name, len(source), sha256(source).hexdigest(), "footer", footer)
    damage = None
    for group_index in range(3):
        verify_group(file, group_index)
        group = file.metadata.row_group(group_index)
        assert group.num_columns == 2 and group.num_rows == 16
        for column_index, encoding in enumerate((3, 9)):
            column = group.column(column_index)
            assert column.path_in_schema == schema.names[column_index]
            assert column.compression == "UNCOMPRESSED" and not column.has_dictionary_page
            assert column.num_values == 16
            cursor = column.data_page_offset
            stop = cursor + column.total_compressed_size
            assert 4 <= cursor < stop <= footer
            observed = []
            while cursor < stop:
                transport = TMemoryBuffer(source[cursor:stop])
                header = header_fields(TCompactProtocol(transport), (5, 8))
                start = cursor + transport.cstringio_buf.tell()
                end = start + header[3]
                assert cursor < start <= end <= stop and header[2] == header[3] and 4 not in header
                if version == "1.0":
                    page = header[5]
                    assert header[1] == 0 and [page[k] for k in (2, 3, 4)] == [encoding, 3, 3]
                    scalar = start + 4 + struct.unpack_from("<I", source, start)[0]
                else:
                    page = header[8]
                    assert header[1] == 3 and [page[k] for k in (3, 4, 6, 7)] == [page[1], encoding, 0, False]
                    scalar = start + page[5]
                first = 16 * group_index + sum(observed)
                values = (booleans if column_index == 0 else floats)[first:first + page[1]]
                if version == "2.0":
                    assert page[2] == values.count(None)
                assert start <= scalar <= end
                if column_index == 0:
                    length = struct.unpack_from("<I", source, scalar)[0]
                    assert scalar + 4 + length == end
                    if (group_index, len(observed)) == (1, 1):
                        damage = cursor, scalar, length
                else:
                    words = [struct.pack("<I", value) for value in values if value is not None]
                    assert source[scalar:end] == bytes(word[lane] for lane in range(4) for word in words)
                print(group_index, column_index, len(observed), "tag", encoding, "count", page[1],
                      "header", cursor, "body", start, end, "scalars", scalar)
                observed.append(page[1])
                cursor = end
            assert cursor == stop and observed == ([4, 4, 4, 4] if column_index == 0 else [12, 4])
    return source, damage


def verify_bad(path, source, damage):
    header, offset, length = damage
    changed = bytearray(source)
    struct.pack_into("<I", changed, offset, length + 1)
    path.write_bytes(changed)
    file = pq.ParquetFile(path)
    verify_group(file, 0)
    verify_group(file, 2)
    try:
        file.read_row_group(1)
    except (OSError, pa.ArrowInvalid) as error:
        print(path.name, sha256(changed).hexdigest(),
              "rejected group 1 column 0 page 1", "header", header, "length at", offset,
              length, "changed to", length + 1, repr(error))
    else:
        raise AssertionError("accepted overdeclared RLE BOOLEAN value length")


for version in ("1.0", "2.0"):
    path = directory / f"mixed-boolean-float-v{version[0]}.parquet"
    pq.write_table(
        table, path, version="2.6", data_page_version=version, compression="NONE",
        use_dictionary=False, column_encoding={"enabled": "RLE", "measurement": "BYTE_STREAM_SPLIT"},
        write_page_checksum=False, write_statistics=False, row_group_size=16, write_batch_size=4,
        data_page_size=32,
    )
    source, damage = verify(path, version)
    if version == "2.0":
        verify_bad(directory / "mixed-boolean-float-v2-bad-length.parquet", source, damage)
