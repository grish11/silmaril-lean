"""Reproduce and inspect the full-file RLE BOOLEAN fixtures."""

import argparse
from hashlib import sha256
from pathlib import Path
from runpy import run_path
import struct

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

ROOT = Path(__file__).resolve().parents[2]
header_fields = run_path(str(ROOT / "scripts/parquet-scalar-page/PyArrowOracle.py"))["header_fields"]
slots = (
    [True] * 8
    + [False, None, True, False, None, True, None, False]
    + [False] * 8
    + [True, None, False, True, None, False, None, True]
    + [True, False, True, False, None, False, True, None]
    + [None] * 8
)
schema = pa.schema([pa.field("enabled", pa.bool_(), nullable=True)])
table = pa.Table.from_arrays([pa.array(slots, type=pa.bool_())], schema=schema)


def verify(path, version):
    source = path.read_bytes()
    file = pq.ParquetFile(path)
    assert file.metadata.num_row_groups == 3
    leaf = file.schema.column(0)
    assert (leaf.physical_type, leaf.max_definition_level, leaf.max_repetition_level) == ("BOOLEAN", 1, 0)
    footer = len(source) - 8 - int.from_bytes(source[-8:-4], "little")
    print(path.name, len(source), sha256(source).hexdigest(), "footer", footer)
    damage = None
    for group_index in range(3):
        group = file.metadata.row_group(group_index)
        assert group.num_columns == 1 and group.num_rows == 16
        group_start = 16 * group_index
        assert file.read_row_group(group_index).column(0).to_pylist() == slots[group_start:group_start + 16]
        column = group.column(0)
        assert column.encodings == ("RLE",) and column.compression == "UNCOMPRESSED"
        assert not column.has_dictionary_page
        cursor = column.data_page_offset
        stop = cursor + column.total_compressed_size
        assert 4 <= cursor < stop <= footer
        for page_index in range(2):
            transport = TMemoryBuffer(source[cursor:stop])
            header = header_fields(TCompactProtocol(transport), (5, 8))
            start = cursor + transport.cstringio_buf.tell()
            end = start + header[3]
            assert cursor < start < end <= stop and header[2] == header[3] and 4 not in header
            offset = group_start + page_index * 8
            nulls = slots[offset:offset + 8].count(None)
            if version == "1.0":
                assert header[1] == 0 and [header[5][i] for i in (1, 2, 3, 4)] == [8, 3, 3, 3]
                value_start = start + 4 + struct.unpack_from("<I", source, start)[0]
            else:
                assert header[1] == 3
                fields = header[8]
                assert [fields[i] for i in (1, 2, 3, 4, 6, 7)] == [8, nulls, 8, 3, 0, False]
                value_start = start + fields[5]
            length = struct.unpack_from("<I", source, value_start)[0]
            assert start <= value_start and value_start + 4 + length == end
            if nulls == 8:
                assert length == 0
            if (group_index, page_index) == (1, 1):
                assert length > 0
                damage = (cursor, value_start, length)
            print(group_index, page_index, "header", cursor, "body", start, end,
                  "valueLength", value_start, length, "runs", source[value_start + 4:end].hex() or "-")
            cursor = end
        assert cursor == stop
    return source, damage


def verify_damaged(path, source, damage):
    header, offset, length = damage
    changed = bytearray(source)
    struct.pack_into("<I", changed, offset, length + 1)
    path.write_bytes(changed)
    file = pq.ParquetFile(path)
    assert file.read_row_group(0).column(0).to_pylist() == slots[:16]
    assert file.read_row_group(2).column(0).to_pylist() == slots[32:]
    try:
        file.read_row_group(1)
    except (OSError, pa.ArrowInvalid) as error:
        print(path.name, sha256(changed).hexdigest(), "rejected group 1 page 1",
              "header", header, "length at", offset, length, "changed to", length + 1, repr(error))
    else:
        raise AssertionError("accepted overdeclared RLE BOOLEAN value length")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    args = parser.parse_args()
    assert pa.__version__ == "26.0.1"
    args.directory.mkdir(parents=True, exist_ok=True)
    for version in ("1.0", "2.0"):
        path = args.directory / f"boolean-rle-v{version[0]}.parquet"
        pq.write_table(
            table, path, version="2.6", data_page_version=version, compression="NONE",
            use_dictionary=False, column_encoding="RLE", write_statistics=False, write_page_checksum=False,
            row_group_size=16, write_batch_size=8, data_page_size=1,
        )
        source, damage = verify(path, version)
        if version == "2.0":
            verify_damaged(args.directory / "boolean-rle-v2-bad-length.parquet", source, damage)


if __name__ == "__main__":
    main()
