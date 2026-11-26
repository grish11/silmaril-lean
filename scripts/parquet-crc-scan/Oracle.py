"""Generate an uncompressed V1 CRC control and verify exact V2 mutations."""

import argparse
from pathlib import Path
from runpy import run_path
import zlib

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

ROOT = Path(__file__).resolve().parents[2]
base = run_path(str(ROOT / "scripts/parquet-dictionary-snapshot/Oracle.py"))
NAMES, VALUES, header_fields = (base[name] for name in ("NAMES", "VALUES", "header_fields"))


def check_v1(path):
    raw = path.read_bytes()
    file = pq.ParquetFile(path, page_checksum_verification=True)
    assert file.read().to_pydict() == dict(zip(NAMES, VALUES))
    for group_index in range(file.metadata.num_row_groups):
        group = file.metadata.row_group(group_index)
        for index in range(group.num_columns):
            column = group.column(index)
            assert column.compression == "UNCOMPRESSED" and column.has_dictionary_page == (index == 1)
            cursor = column.dictionary_page_offset if index == 1 else column.data_page_offset
            stop = cursor + column.total_compressed_size
            while cursor < stop:
                transport = TMemoryBuffer(raw[cursor:stop])
                header = header_fields(TCompactProtocol(transport), (5, 7))
                body_start = cursor + transport.cstringio_buf.tell()
                body_stop = body_start + header[3]
                assert body_stop <= stop and header[4] & 0xffffffff == zlib.crc32(raw[body_start:body_stop])
                if index == 1 and cursor == column.dictionary_page_offset:
                    assert header[1] == 2 and header[7][2] == 0
                else:
                    assert header[1] == 0 and header[5][2] == (0 if index == 0 else 8)
                cursor = body_stop
            assert cursor == stop


def mutations():
    raw = (ROOT / "data/parquet-dictionary-snapshot/crc-plain-v2.parquet").read_bytes()
    file = pq.ParquetFile(pa.BufferReader(raw), page_checksum_verification=True)
    assert file.read().to_pydict() == dict(zip(NAMES, VALUES))
    group = file.metadata.row_group(1)
    for column_index in range(group.num_columns):
        column = group.column(column_index)
        cursor = column.dictionary_page_offset if column.has_dictionary_page else column.data_page_offset
        stop = cursor + column.total_compressed_size
        index = 0
        while cursor < stop:
            transport = TMemoryBuffer(raw[cursor:stop])
            header = header_fields(TCompactProtocol(transport), (7, 8))
            body_start = cursor + transport.cstringio_buf.tell()
            body_stop = body_start + header[3]
            crc = header[4] & 0xffffffff
            assert body_stop <= stop and crc == zlib.crc32(raw[body_start:body_stop])
            cases = {}
            if column_index == 0 and index == 1:
                cases["plainSecond"] = body_start
            if column_index == 1 and index == 0:
                assert header[1] == 2
                cases["dictionary"] = body_start
            if column_index == 1 and index == 1:
                assert header[1] == 3 and header[8][6] == 0 and header[8][5] > 0
                cases["definitions"] = body_start
                cases["indices"] = body_start + header[8][5]
            for label, byte in cases.items():
                assert byte < body_stop
                damaged = bytearray(raw)
                damaged[byte] ^= 1
                computed = zlib.crc32(damaged[body_start:body_stop])
                broken = pq.ParquetFile(pa.BufferReader(damaged), page_checksum_verification=True)
                assert broken.read_row_group(0).to_pydict() == dict(zip(NAMES, [col[:8] for col in VALUES]))
                try:
                    broken.read_row_group(1)
                except OSError as error:
                    assert "CRC" in str(error)
                else:
                    raise AssertionError(f"accepted CRC mutation: {label}")
                print(label, byte, column_index, index, cursor, crc, computed, sep="\t")
            index += 1
            cursor = body_stop
        assert cursor == stop


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    assert pa.__version__ == "26.0.1"
    path = args.directory / "crc-mixed-v1.parquet"
    if args.write:
        schema = pa.schema([pa.field(name, pa.int32(), nullable=bool(i)) for i, name in enumerate(NAMES)])
        table = pa.Table.from_arrays([pa.array(values, type=pa.int32()) for values in VALUES], schema=schema)
        pq.write_table(table, path, version="2.6", data_page_version="1.0", compression="NONE",
                       use_dictionary=[NAMES[1]], write_statistics=False, write_page_checksum=True,
                       row_group_size=8, write_batch_size=4, data_page_size=1)
    check_v1(path)
    mutations()


if __name__ == "__main__":
    main()
