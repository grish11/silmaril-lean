"""Generate and independently check mixed dictionary/PLAIN snapshot files."""

import argparse
from pathlib import Path
from runpy import run_path
import zlib

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

header_fields = run_path(str(Path(__file__).resolve().parents[1] /
                             "parquet-flat-page" / "PyArrowOracle.py"))["header_fields"]
NAMES = ["required_i32", "optional_i32"]
VALUES = [[100 + i for i in range(16)],
          [None if i % 4 == 0 else 40 * (i // 8) - 9 + 3 * (i % 3) for i in range(16)]]


def check(path, dict_column, codec, crc):
    raw = path.read_bytes()
    file = pq.ParquetFile(path, page_checksum_verification=crc)
    assert file.read().to_pydict() == dict(zip(NAMES, VALUES))
    assert file.metadata.num_row_groups == 2 and file.metadata.num_rows == 16
    corrupt_at = None
    for group_index in range(2):
        group = file.metadata.row_group(group_index)
        assert group.num_rows == 8 and group.num_columns == 2
        for column_index, name in enumerate(NAMES):
            column = group.column(column_index)
            dictionary = column_index == dict_column
            assert column.path_in_schema == name and column.has_dictionary_page == dictionary
            assert column.compression == codec and column.num_values == 8
            cursor = column.dictionary_page_offset if dictionary else column.data_page_offset
            stop = cursor + column.total_compressed_size
            first_data = True
            while cursor < stop:
                transport = TMemoryBuffer(raw[cursor:stop])
                header = header_fields(TCompactProtocol(transport), (7, 8))
                body_start = cursor + transport.cstringio_buf.tell()
                body_stop = body_start + header[3]
                assert body_start <= body_stop <= stop and (4 in header) == crc
                if crc:
                    assert header[4] & 0xffffffff == zlib.crc32(raw[body_start:body_stop])
                if dictionary and cursor == column.dictionary_page_offset:
                    assert header[1] == 2 and header[7][2] == 0
                    assert body_stop == column.data_page_offset
                else:
                    assert header[1] == 3 and header[8][4] == (8 if dictionary else 0)
                    if first_data:
                        assert cursor == column.data_page_offset
                        if group_index == 1 and dictionary and not crc and codec == "UNCOMPRESSED":
                            assert header[8][6] == 0
                            corrupt_at = body_start + header[8][5]
                            assert corrupt_at < body_stop and raw[corrupt_at] <= 32
                    first_data = False
                cursor = body_stop
            assert cursor == stop and not first_data
    if corrupt_at is not None:
        corrupt = raw[:corrupt_at] + bytes([33]) + raw[corrupt_at + 1:]
        corrupted = pq.ParquetFile(pa.BufferReader(corrupt))
        assert corrupted.read_row_group(0).to_pydict() == {
            name: values[:8] for name, values in zip(NAMES, VALUES)
        }
        try:
            corrupted.read_row_group(1)
        except OSError as error:
            assert "Invalid or corrupted bit_width 33" in str(error)
        else:
            raise AssertionError("accepted corrupted dictionary index width")
        print(f"{path.name}: invalid width at {corrupt_at} preserves group 0 and rejects group 1")
    else:
        print(f"{path.name}: independent rows and page headers verified")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    assert pa.__version__ == "26.0.1"
    schema = pa.schema([pa.field(name, pa.int32(), nullable=bool(i))
                        for i, name in enumerate(NAMES)])
    table = pa.Table.from_arrays([pa.array(x, type=pa.int32()) for x in VALUES], schema=schema)
    cases = [("mixed-v2", 1, "UNCOMPRESSED", False), ("crc-plain-v2", 1, "UNCOMPRESSED", True),
             ("crc-dictionary-v2", 0, "UNCOMPRESSED", True), ("snappy-plain-v2", 1, "SNAPPY", False),
             ("snappy-dictionary-v2", 0, "SNAPPY", False)]
    for case, dictionary, codec, crc in cases:
        path = args.directory / f"{case}.parquet"
        if args.write:
            compression = "NONE" if codec == "UNCOMPRESSED" else codec
            pq.write_table(table, path, version="2.6", data_page_version="2.0", compression=compression,
                           use_dictionary=[NAMES[dictionary]], write_statistics=False,
                           write_page_checksum=crc, row_group_size=8, write_batch_size=4,
                           data_page_size=1)
        check(path, dictionary, codec, crc)


if __name__ == "__main__":
    main()
