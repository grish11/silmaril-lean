"""Pin real PyArrow dictionary fallback and same-source negative controls."""
from hashlib import sha256
from importlib.metadata import version
from pathlib import Path
from runpy import run_path
import struct
import sys

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

assert (version("pyarrow"), version("thrift")) == ("26.0.1", "0.25.0")
root = Path(__file__).resolve().parents[2]
thrift = run_path(str(root / "tests/formats/parquet-timestamp-leaf/check-fixtures.py"))
schema = pa.schema([pa.field("ordinal", pa.int32(), nullable=False), pa.field("payload", pa.binary())])
group_size = 384
values = [
    [
        None if row % 13 == 5 else
        ((b"\x00\xff" if row % 2 == 0 else b"") + bytes([group])) if row < 256 else
        f"distinct-{row:04d}-".encode() + b"opaque-value-\xff" * 4 + bytes([group])
        for row in range(group_size)
    ]
    for group in range(2)
]


def produce(page_version):
    table = pa.Table.from_arrays([
        pa.array(range(2 * group_size), pa.int32()),
        pa.array(sum(values, []), pa.binary()),
    ], schema=schema)
    sink = pa.BufferOutputStream()
    pq.write_table(table, sink, version="2.6", data_page_version=f"{page_version}.0",
                   compression="NONE", use_dictionary=["payload"], dictionary_pagesize_limit=96,
                   data_page_size=32, write_batch_size=16, row_group_size=group_size,
                   write_statistics=False, write_page_checksum=False, store_schema=False)
    return sink.getvalue().to_pybytes()


def inspect(wire, index, page_version):
    with pq.ParquetFile(pa.BufferReader(wire)) as file:
        column = file.metadata.row_group(index).column(1)
        assert column.path_in_schema == "payload" and column.physical_type == "BYTE_ARRAY"
        assert column.compression == "UNCOMPRESSED" and column.has_dictionary_page
    start = column.dictionary_page_offset
    stop = start + column.total_compressed_size
    memory = TMemoryBuffer(wire[start:stop])
    protocol = TCompactProtocol(memory)
    frames = []
    while (header := start + memory.cstringio_buf.tell()) < stop:
        fields = thrift["read_struct"](protocol)
        body = start + memory.cstringio_buf.tell()
        end = body + fields[3][1]
        assert 4 not in fields and fields[2] == fields[3] and end <= stop
        if not frames:
            assert fields[1][1] == 2 and fields[7][1][2][1] == 0
        elif page_version == 1:
            assert fields[1][1] == 0 and fields[5][1][3][1] == fields[5][1][4][1] == 3
        else:
            assert fields[1][1] == 3 and fields[8][1][6][1] == 0
        memory.readAll(fields[3][1])
        frames.append((header, body, end, fields))
    assert start + memory.cstringio_buf.tell() == stop and frames[1][0] == column.data_page_offset
    key, tag_field = (5, 2) if page_version == 1 else (8, 4)
    tags = [fields[key][1][tag_field][1] for _, _, _, fields in frames[1:]]
    assert tags == [8] * 17 + [0] * 7
    assert sum(fields[key][1][1][1] for _, _, _, fields in frames[1:]) == group_size
    print(f"V{page_version} group {index}: dictionary header {frames[0][0]}, data offset {frames[1][0]}, 17 tag 8 then 7 tag 0")
    return frames


def readback(wire, index):
    with pq.ParquetFile(pa.BufferReader(wire)) as file:
        assert file.schema_arrow == schema and file.num_row_groups == 2
        table = file.read_row_group(index, columns=["payload"], use_threads=False)
        assert table.column(0).to_pylist() == values[index]


def missing_dictionary(wire, frames):
    removed_bytes = frames[1][0] - frames[0][0]

    def remove(metadata):
        column = thrift["column_metadata"](metadata, group=1, column=1)
        assert column.pop(11) == (TType.I64, frames[0][0])
        for size in (6, 7):
            column[size] = (TType.I64, column[size][1] - removed_bytes)
        group = thrift["list_field"](metadata, 4)[1]
        for size in (2, 6):
            if size in group:
                group[size] = (TType.I64, group[size][1] - removed_bytes)

    return thrift["rewrite_footer"](wire, remove)


def wrong_encoding(wire, frame):
    header, body, _, fields = frame
    fields[8][1][4] = TType.I32, 3
    replacement = thrift["encode"](fields)
    assert len(replacement) == body - header
    return wire[:header] + replacement + wire[body:]


def wrong_length(wire, frame):
    _, body, end, fields = frame
    start = body + fields[8][1][5][1]
    assert fields[8][1][4][1] == 0 and start + 4 < end
    assert 0 <= struct.unpack_from("<i", wire, start)[0] < end - start - 4
    return wire[:start] + struct.pack("<i", -1) + wire[start + 4:]


def reject(wire):
    readback(wire, 0)
    with pq.ParquetFile(pa.BufferReader(wire)) as file:
        try:
            file.read_row_group(1, columns=["payload"], use_threads=False)
        except (OSError, pa.ArrowInvalid):
            return
    raise AssertionError("PyArrow admitted damaged group")


out = Path(sys.argv[1])
out.mkdir(parents=True, exist_ok=True)
for version_number in (1, 2):
    wire = produce(version_number)
    for group in range(2):
        frames = inspect(wire, group, version_number)
        readback(wire, group)
    cases = [(f"byte-array-fallback-v{version_number}.parquet", wire)]
    if version_number == 2:
        for name, damaged, ordinal, header in [
            ("missing-dictionary", missing_dictionary(wire, frames), 0, frames[1][0]),
            ("bad-tag", wrong_encoding(wire, frames[19]), 19, frames[19][0]),
            ("bad-length", wrong_length(wire, frames[24]), 24, frames[24][0]),
        ]:
            reject(damaged)
            print(f"{name}: group 1, column 1, page {ordinal}, header {header}")
            cases.append((f"byte-array-fallback-v2-{name}.parquet", damaged))
    for name, source in cases:
        print(f"{sha256(source).hexdigest()}  {name}")
        (out / name).write_bytes(source)
