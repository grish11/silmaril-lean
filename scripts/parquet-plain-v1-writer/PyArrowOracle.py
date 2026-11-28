"""Read emitted V1 pages with pinned Compact and PyArrow fixture readers."""
import argparse
import hashlib
from pathlib import Path
from runpy import run_path
import struct

import numpy as np
import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer


SCRIPTS = Path(__file__).resolve().parents[1]
SCALAR = run_path(str(SCRIPTS / "parquet-scalar-page" / "PyArrowOracle.py"))
header_fields = SCALAR["header_fields"]
CASES = {
    "required": (False, [-2147483648, 0, 2147483647]),
    "mixed": (True, [7, None, -4, None, 19]),
    "all-null": (True, [None, None, None]),
    "required-empty": (False, []),
    "optional-empty": (True, []),
}


def fixture_with_page(nullable, values, page):
    """Replace the only data page of a PyArrow fixture and adjust its footer sizes."""
    schema = pa.schema([pa.field("v", pa.int32(), nullable=nullable)])
    table = pa.Table.from_arrays([pa.array(values, type=pa.int32())], schema=schema)
    sink = pa.BufferOutputStream()
    pq.write_table(table, sink, compression="NONE", data_page_version="1.0", version="2.6",
                   row_group_size=len(values), use_dictionary=False, column_encoding="PLAIN",
                   write_statistics=False, write_page_index=False, write_page_checksum=False)
    seed = sink.getvalue().to_pybytes()
    reader = pq.ParquetFile(pa.BufferReader(seed))
    assert reader.read().column(0).to_pylist() == values
    assert reader.metadata.num_row_groups == 1
    column = reader.metadata.row_group(0).column(0)
    footer_size = struct.unpack_from("<I", seed, len(seed) - 8)[0]
    footer_start = len(seed) - 8 - footer_size
    assert column.data_page_offset == 4 and column.total_compressed_size == footer_start - 4
    assert column.total_uncompressed_size == column.total_compressed_size
    if not nullable:
        scalar_bytes = len(values) * 4
        assert page[-scalar_bytes:] == seed[footer_start - scalar_bytes:footer_start]
    footer = seed[footer_start:-8]

    encoded_length = TMemoryBuffer()
    encoder = TCompactProtocol(encoded_length)
    encoder.writeStructBegin("")
    encoder.writeFieldBegin("", TType.I64, 1)
    field_start = len(encoded_length.getvalue())
    encoder.writeI64(len(page))
    new_length = encoded_length.getvalue()[field_start:]
    source = TMemoryBuffer(footer)
    protocol = TCompactProtocol(source)
    patches = []

    def record_size():
        start = source.cstringio_buf.tell()
        assert protocol.readI64() == column.total_compressed_size
        patches.append((start, source.cstringio_buf.tell()))

    def one_struct(read):
        assert protocol.readListBegin() == (TType.STRUCT, 1)
        read()
        protocol.readListEnd()

    def fields(visit, sizes=()):
        protocol.readStructBegin()
        while True:
            _, ty, field = protocol.readFieldBegin()
            if ty == TType.STOP:
                break
            if field in sizes:
                assert ty == TType.I64
                record_size()
            elif field in visit:
                visit[field]()
            else:
                protocol.skip(ty)
            protocol.readFieldEnd()
        protocol.readStructEnd()

    def chunk():
        fields({3: lambda: fields({}, (6, 7))})

    def group():
        fields({1: lambda: one_struct(chunk)}, (2, 6))

    fields({4: lambda: one_struct(group)})
    assert len(patches) in (3, 4)
    for start, stop in reversed(patches):
        footer = footer[:start] + new_length + footer[stop:]
    return b"PAR1" + page + footer + struct.pack("<I", len(footer)) + b"PAR1"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    args = parser.parse_args()
    assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
    assert np.__version__ == "2.5.5"
    for name, (nullable, values) in CASES.items():
        page = (args.directory / f"{name}.page").read_bytes()
        transport = TMemoryBuffer(page)
        header = header_fields(TCompactProtocol(transport), (5,))
        offset = transport.cstringio_buf.tell()
        body = page[offset:]
        assert header == {1: 0, 2: len(body), 3: len(body), 5: {1: len(values), 2: 0, 3: 3, 4: 3}}
        if values:
            fixture = fixture_with_page(nullable, values, page)
            reader = pq.ParquetFile(pa.BufferReader(fixture))
            assert reader.metadata.row_group(0).column(0).total_compressed_size == len(page)
            assert reader.read().column(0).to_pylist() == values
            (args.directory / f"{name}.parquet").write_bytes(fixture)
        else:
            assert body == (b"\0" * 4 if nullable else b"")
        print(f"{name}: {len(values)} rows, {offset}+{len(body)} bytes, "
              f"SHA-256 {hashlib.sha256(page).hexdigest()}")


if __name__ == "__main__":
    main()
