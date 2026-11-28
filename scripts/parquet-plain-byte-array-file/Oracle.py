"""Write and independently check whole-file flat PLAIN BYTE_ARRAY fixtures."""
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
page_oracle = Path(__file__).resolve().parents[1] / "parquet-scalar-page" / "PyArrowOracle.py"
header_fields = run_path(str(page_oracle))["header_fields"]
directory = Path(sys.argv[1])
directory.mkdir(parents=True, exist_ok=True)

ROWS = 12
GROUPS = 3
OPTIONAL = [
    b"", None, b"\xff\0\x80", b"x" * 48,
    None, None, None, None,
    b"\x00", b"\xc3\xa9", None, b"y" * 36,
]
optional = [
    value if value in (None, b"") else value + bytes([group])
    for group in range(GROUPS) for value in OPTIONAL
]
required = [
    b"" if row == 0 else bytes([0x80 + group, row]) * (1 + row % 5)
    for group in range(GROUPS) for row in range(ROWS)
]
schema = pa.schema([
    pa.field("ordinal", pa.int32(), nullable=False),
    pa.field("payload", pa.binary(), nullable=True),
    pa.field("key", pa.binary(), nullable=False),
])
table = pa.Table.from_arrays([
    pa.array(range(ROWS * GROUPS), type=pa.int32()),
    pa.array(optional, type=pa.binary()), pa.array(required, type=pa.binary()),
], schema=schema)


def verify_group(file, group, expected_columns=("payload", "key")):
    batch = file.read_row_group(group, columns=list(expected_columns), use_threads=False)
    start = group * ROWS
    for name in expected_columns:
        values = optional if name == "payload" else required
        assert batch[name].to_pylist() == values[start:start + ROWS]


def verify(path, version):
    source = path.read_bytes()
    file = pq.ParquetFile(path)
    assert file.metadata.num_row_groups == GROUPS and file.metadata.num_rows == ROWS * GROUPS
    for ordinal, depth in ((1, 1), (2, 0)):
        leaf = file.schema.column(ordinal)
        assert leaf.physical_type == "BYTE_ARRAY" and leaf.logical_type.type == "NONE"
        assert leaf.max_definition_level == depth and leaf.max_repetition_level == 0
    footer = len(source) - 8 - int.from_bytes(source[-8:-4], "little")
    damage = None
    for group_index in range(GROUPS):
        verify_group(file, group_index)
        group = file.metadata.row_group(group_index)
        assert group.num_rows == ROWS
        for ordinal, values in ((1, optional), (2, required)):
            column = group.column(ordinal)
            assert column.path_in_schema == schema.names[ordinal]
            assert column.compression == "UNCOMPRESSED" and not column.has_dictionary_page
            assert column.num_values == ROWS and set(column.encodings) <= {"RLE", "PLAIN"}
            cursor = column.data_page_offset
            stop = cursor + column.total_compressed_size
            assert 4 <= cursor < stop <= footer
            assert column.total_uncompressed_size == column.total_compressed_size
            counts = []
            while cursor < stop:
                transport = TMemoryBuffer(source[cursor:stop])
                header = header_fields(TCompactProtocol(transport), (5, 8))
                start = cursor + transport.cstringio_buf.tell()
                end = start + header[3]
                assert cursor < start <= end <= stop and header[2] == header[3] and 4 not in header
                if version == "1.0":
                    page = header[5]
                    assert header[1] == 0 and [page[k] for k in (2, 3, 4)] == [0, 3, 3]
                    scalar = start + (4 + struct.unpack_from("<I", source, start)[0] if ordinal == 1 else 0)
                else:
                    page = header[8]
                    assert header[1] == 3 and [page[k] for k in (3, 4, 6, 7)] == [page[1], 0, 0, False]
                    scalar = start + page[5]
                    if ordinal == 2:
                        assert page[5] == 0
                first = ROWS * group_index + sum(counts)
                slots = values[first:first + page[1]]
                if version == "2.0":
                    assert page[2] == slots.count(None)
                assert start <= scalar <= end
                present = [value for value in slots if value is not None]
                assert source[scalar:end] == b"".join(struct.pack("<i", len(v)) + v for v in present)
                if ordinal == 1 and group_index == 1 and len(counts) > 0 and present and damage is None:
                    damage = cursor, scalar, len(present[0]), len(counts)
                print(version, group_index, ordinal, len(counts), page[1], "header", cursor,
                      "body", start, end, "scalar", scalar)
                counts.append(page[1])
                cursor = end
            assert cursor == stop and sum(counts) == ROWS
            if ordinal == 1:
                assert len(counts) > 1
    assert damage is not None
    print(path.name, len(source), sha256(source).hexdigest())
    return source, damage


def verify_bad(path, source, damage):
    header, offset, length, page = damage
    changed = bytearray(source)
    struct.pack_into("<I", changed, offset, 0xFFFF)
    path.write_bytes(changed)
    file = pq.ParquetFile(path)
    verify_group(file, 0)
    verify_group(file, 1, ("key",))
    verify_group(file, 2)
    try:
        file.read_row_group(1, columns=["payload"], use_threads=False)
    except (OSError, pa.ArrowInvalid) as error:
        print(path.name, len(source), sha256(changed).hexdigest(),
              "rejected group 1 column 1 page", page, "header", header, "length at", offset,
              length, "changed to 65535", repr(error))
    else:
        raise AssertionError("accepted overdeclared PLAIN BYTE_ARRAY value length")


for version in ("1.0", "2.0"):
    prefix = f"plain-byte-array-v{version[0]}"
    path = directory / f"{prefix}.parquet"
    pq.write_table(
        table, path, version="2.6", data_page_version=version, compression="NONE",
        use_dictionary=False, column_encoding="PLAIN", write_statistics=False,
        write_page_checksum=False, row_group_size=ROWS, write_batch_size=4, data_page_size=32,
    )
    source, damage = verify(path, version)
    verify_bad(directory / f"{prefix}-bad-length.parquet", source, damage)
