"""Reproduce PyArrow files and inspect both writers with PyArrow and Thrift."""

import argparse
from pathlib import Path
from runpy import run_path
import struct

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

header_fields = run_path(str(Path(__file__).resolve().parents[1] /
                             "parquet-flat-page" / "PyArrowOracle.py"))["header_fields"]


def arrow_columns():
    return {
        "required_i32": [100 * (i // 24) + (i % 3 if i % 24 < 8 else i % 24) for i in range(48)],
        "optional_i32": [None if i < 24 or i % 4 == 0 else -9 + 7 * (i % 5)
                         for i in range(48)],
    }


def java_columns():
    return {
        "required_i32": [17 - 11 * (i % 3) for i in range(192)],
        "optional_i32": [None if i % 4 == 0 else -9 + 7 * (i % 5) for i in range(192)],
    }


def write_arrow(directory, cols):
    schema = pa.schema([pa.field("required_i32", pa.int32(), nullable=False),
                        pa.field("optional_i32", pa.int32(), nullable=True)])
    table = pa.Table.from_pydict(cols, schema=schema)
    for version in (1, 2):
        pq.write_table(table, directory / f"arrow-v{version}.parquet", version="2.6",
                       data_page_version=f"{version}.0", compression="NONE", use_dictionary=True,
                       write_statistics=False, write_page_checksum=False, row_group_size=24,
                       write_batch_size=8, data_page_size=1, dictionary_pagesize_limit=24)


def observe(path, cols, version):
    raw = path.read_bytes()
    parquet = pq.ParquetFile(path)
    assert parquet.read().to_pydict() == cols
    assert parquet.metadata.created_by.startswith(
        "parquet-mr version 1.16.0" if path.name.startswith("java") else "parquet-cpp-arrow version 26.0.1")
    total = 0
    for index in range(parquet.metadata.num_row_groups):
        group = parquet.metadata.row_group(index)
        for col_index, (name, column) in enumerate(cols.items()):
            metadata = group.column(col_index)
            assert metadata.path_in_schema == name and metadata.physical_type == "INT32"
            assert metadata.compression == "UNCOMPRESSED" and metadata.has_dictionary_page
            assert metadata.num_values == group.num_rows
            start = metadata.dictionary_page_offset
            stop = start + metadata.total_compressed_size
            offsets, encodings, counts = [], [], []
            cursor = start
            while cursor < stop:
                transport = TMemoryBuffer(raw[cursor:stop])
                header = header_fields(TCompactProtocol(transport), (5, 7, 8))
                assert header[2] == header[3] and 4 not in header
                body_start = cursor + transport.cstringio_buf.tell()
                body_stop = body_start + header[3]
                assert body_start <= body_stop <= stop
                kind = header[1]
                if cursor == start:
                    assert kind == 2
                    detail = header[7]
                    entries = [v for v, in struct.iter_unpack("<i", raw[body_start:body_stop])]
                    assert len(entries) == detail[1]
                    assert entries == list(dict.fromkeys(v for v in column[total:total + group.num_rows]
                                                        if v is not None))[:len(entries)]
                    assert detail[2] == (2 if path.name == "java-v1.parquet" else 0)
                    assert body_stop == metadata.data_page_offset
                else:
                    assert kind == (0 if version == 1 else 3)
                    detail = header[5 if version == 1 else 8]
                    if version == 1:
                        assert detail[3] in ((3,) if col_index == 1 else (3, 4))
                        assert detail[4] in (3, 4)
                    else:
                        assert detail[1] == detail[3] and detail[6] == 0
                        page_start = total + sum(counts)
                        assert detail[2] == column[page_start:page_start + detail[1]].count(None)
                    encodings.append(detail[2 if version == 1 else 4])
                    counts.append(detail[1])
                offsets.append((cursor, body_start, body_stop))
                cursor = body_stop
            assert cursor == stop and sum(counts) == group.num_rows
            assert encodings[0] == (2 if path.name == "java-v1.parquet" else 8)
            windows = ",".join(f"{start}:{body}:{stop}" for start, body, stop in offsets)
            print(path.name, index, name, windows, ",".join(map(str, entries)),
                  ",".join(map(str, encodings)), ",".join(map(str, counts)), sep="\t")
        total += group.num_rows
    assert total == len(next(iter(cols.values())))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--write-arrow", action="store_true")
    args = parser.parse_args()
    assert pa.__version__ == "26.0.1"
    if args.write_arrow:
        write_arrow(args.directory, arrow_columns())
    for name, cols in [("arrow", arrow_columns()), ("java", java_columns())]:
        for version in (1, 2):
            observe(args.directory / f"{name}-v{version}.parquet", cols, version)


if __name__ == "__main__":
    main()
