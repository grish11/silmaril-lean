"""Reproduce flat multi-group PLAIN/DELTA_BINARY_PACKED files with pinned PyArrow and Thrift."""
import argparse
from hashlib import sha256
from pathlib import Path
from runpy import run_path

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

ROOT = Path(__file__).resolve().parents[2]
header_fields = run_path(str(ROOT / "scripts/parquet-flat-page/PyArrowOracle.py"))["header_fields"]
SCHEMA = pa.schema(
    [pa.field("required_i32", pa.int32(), nullable=False), pa.field("optional_i32", pa.int32())]
)
TABLE = pa.Table.from_pydict(
    {"required_i32": list(range(-8, 16)),
     "optional_i32": [None if i % 4 == 1 else 300 - i * i for i in range(24)]},
    schema=SCHEMA,
)


def emit(directory, version):
    path = directory / f"plain-delta-v{version[0]}.parquet"
    pq.write_table(
        TABLE, path, version="2.6", data_page_version=version, compression="NONE",
        use_dictionary=False,
        column_encoding={"required_i32": "PLAIN", "optional_i32": "DELTA_BINARY_PACKED"},
        row_group_size=8, write_batch_size=4, data_page_size=1, write_statistics=False,
        write_page_checksum=False,
    )
    return path


def verify(path, version):
    raw = path.read_bytes()
    parquet = pq.ParquetFile(path)
    assert parquet.read().equals(TABLE)
    assert parquet.metadata.num_row_groups == 3
    footer_start = len(raw) - 8 - int.from_bytes(raw[-8:-4], "little")
    print(path.name, len(raw), sha256(raw).hexdigest())
    damage = None
    for group_index in range(3):
        group = parquet.metadata.row_group(group_index)
        assert group.num_rows == 8 and group.num_columns == 2
        for column_index, encoding in enumerate((0, 5)):
            column = group.column(column_index)
            assert column.compression == "UNCOMPRESSED" and not column.has_dictionary_page
            assert column.num_values == group.num_rows
            cursor = column.data_page_offset
            stop = cursor + column.total_compressed_size
            assert 4 <= cursor < stop <= footer_start
            for page_index in range(2):
                transport = TMemoryBuffer(raw[cursor:stop])
                header = header_fields(TCompactProtocol(transport), (5, 8))
                start = cursor + transport.cstringio_buf.tell()
                end = start + header[3]
                assert header[2] == header[3] and 4 not in header
                assert cursor < start <= end <= stop
                if version == "1.0":
                    assert header[1] == 0
                    assert [header[5][key] for key in (1, 2, 3, 4)] == [4, encoding, 3, 3]
                else:
                    assert header[1] == 3
                    data = header[8]
                    assert [data[key] for key in (1, 2, 3, 4, 6)] == [4, column_index, 4, encoding, 0]
                    if (group_index, column_index, page_index) == (1, 1, 1):
                        scalars = start + data[5]
                        # Unsigned VLQs: block size 128, four miniblocks, three present values.
                        assert raw[scalars:scalars + 4] == bytes([0x80, 1, 4, 3])
                        damage = (cursor, scalars + 3)
                print(group_index, column_index, page_index, encoding, cursor, start, end, sep="\t")
                cursor = end
            assert cursor == stop
    if version == "2.0":
        header, byte = damage
        return byte, header


def emit_damaged(path, original, byte, header):
    damaged = bytearray(original.read_bytes())
    damaged[byte] = 0
    path.write_bytes(damaged)
    parquet = pq.ParquetFile(path)
    assert parquet.read_row_group(0).equals(TABLE.slice(0, 8))
    try:
        parquet.read_row_group(1)
    except OSError as error:
        print("PyArrow rejected group 1:", error)
    else:
        raise AssertionError("expected a malformed delta scalar count")
    assert parquet.read_row_group(2).equals(TABLE.slice(16, 8))
    print(path.name, len(damaged), sha256(damaged).hexdigest())
    print("Damaged count at byte", byte, "in group 1 column 1 page 1, header at", header)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    args = parser.parse_args()
    assert pa.__version__ == "26.0.1"
    args.directory.mkdir(parents=True, exist_ok=True)
    verify(emit(args.directory, "1.0"), "1.0")
    v2 = emit(args.directory, "2.0")
    byte, header = verify(v2, "2.0")
    emit_damaged(args.directory / "plain-delta-v2-bad-count.parquet", v2, byte, header)


if __name__ == "__main__":
    main()
