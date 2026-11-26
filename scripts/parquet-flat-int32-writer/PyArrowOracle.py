"""Read complete emitted files with PyArrow and the Apache Thrift Compact reader."""
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
fields = run_path(str(SCRIPTS / "parquet-payload-oracle" / "check.py"))["fields"]
header_fields = run_path(str(SCRIPTS / "parquet-scalar-page" / "PyArrowOracle.py"))["header_fields"]
I32 = (TType.I32, TCompactProtocol.readI32)
I64 = (TType.I64, TCompactProtocol.readI64)
TEXT = (TType.STRING, TCompactProtocol.readString)
CASES = {
    "mixed": [("id", False, [-2147483648, 0, 2147483647]),
              ("café", True, [7, None, -4]), ("nulls", True, [None, None, None])],
    "empty": [("id", False, []), ("optional", True, [])],
    "wide": [(f"v{i}", False, [i]) for i in range(15)],
}


def sequence(tag, read):
    def run(protocol):
        element, count = protocol.readListBegin()
        assert element == tag
        values = [read(protocol) for _ in range(count)]
        protocol.readListEnd()
        return values
    return (TType.LIST, run)


def column_chunk(protocol):
    def column(reader):
        return fields(reader, {1: I32, 2: sequence(*I32), 3: sequence(*TEXT),
                               4: I32, 5: I64, 6: I64, 7: I64, 9: I64})
    return fields(protocol, {2: I64, 3: (TType.STRUCT, column)})


def read_footer(data, columns):
    def schema_element(reader, root):
        return fields(reader, {4: TEXT, 5: I32} if root else {1: I32, 3: I32, 4: TEXT})

    def schema(reader):
        element, count = reader.readListBegin()
        assert (element, count) == (TType.STRUCT, len(columns) + 1)
        nodes = [schema_element(reader, i == 0) for i in range(count)]
        reader.readListEnd()
        return nodes

    def row_group(reader):
        return fields(reader, {1: sequence(TType.STRUCT, column_chunk), 2: I64, 3: I64})

    assert data[:4] == data[-4:] == b"PAR1"
    length = struct.unpack_from("<I", data, len(data) - 8)[0]
    start = len(data) - 8 - length
    assert 4 <= start and length > 0
    transport = TMemoryBuffer(data[start:-8])
    footer = fields(TCompactProtocol(transport),
                    {1: I32, 2: (TType.LIST, schema), 3: I64, 4: sequence(TType.STRUCT, row_group)})
    assert transport.cstringio_buf.tell() == length
    return start, footer


def check(path, columns):
    data = path.read_bytes()
    row_count = len(columns[0][2])
    start, footer = read_footer(data, columns)
    assert footer[1] == 1 and footer[3] == row_count
    assert footer[2] == [{4: "schema", 5: len(columns)}] + [
        {1: 1, 3: int(nullable), 4: name} for name, nullable, _ in columns]
    (group,) = footer[4]
    assert group[2] == start - 4 and group[3] == row_count
    cursor = 4
    for fields_, (name, _, _) in zip(group[1], columns, strict=True):
        assert fields_[2] == 0
        chunk = fields_[3]
        assert chunk[1] == 1 and chunk[2] == [0, 3] and chunk[3] == [name] and chunk[4] == 0
        assert chunk[5] == row_count and chunk[6] == chunk[7] and chunk[9] == cursor
        stop = cursor + chunk[7]
        transport = TMemoryBuffer(data[cursor:stop])
        page = header_fields(TCompactProtocol(transport), (5,))
        size = stop - cursor - transport.cstringio_buf.tell()
        assert page == {1: 0, 2: size, 3: size, 5: {1: row_count, 2: 0, 3: 3, 4: 3}}
        cursor = stop
    assert cursor == start
    reader = pq.ParquetFile(pa.BufferReader(data))
    assert reader.metadata.num_row_groups == 1
    batch = reader.read_row_group(0)
    assert batch.schema == pa.schema([pa.field(name, pa.int32(), nullable=nullable)
                                      for name, nullable, _ in columns])
    assert batch.num_rows == row_count
    assert [column.to_pylist() for column in batch.columns] == [values for _, _, values in columns]
    print(f"{path.stem}: {row_count} rows, {len(columns)} columns, footer={start}:{len(data)-8}, "
          f"{len(data)} bytes, SHA-256 {hashlib.sha256(data).hexdigest()}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    args = parser.parse_args()
    assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
    assert np.__version__ == "2.5.5"
    for name, columns in CASES.items():
        check(args.directory / f"{name}.parquet", columns)


if __name__ == "__main__":
    main()
