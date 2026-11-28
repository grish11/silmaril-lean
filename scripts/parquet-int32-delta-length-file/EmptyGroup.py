"""Exercise a checked empty tag-6 group with an exact zero-count delta stream."""
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

assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"

root = Path(__file__).resolve().parents[2]
thrift = run_path(str(root / "tests/formats/parquet-timestamp-leaf/check-fixtures.py"))
source = (root / "data/parquet-int32-delta-length-group/plain-int32-delta-length-v2.parquet").read_bytes()
transport = TMemoryBuffer(source[729:])
header = thrift["read_struct"](TCompactProtocol(transport))
data = header[8][1]
body = 729 + transport.cstringio_buf.tell()
scalar = source[body + data[5][1]:body + header[3][1]]
assert data[1][1] == data[2][1] == 4 and data[4][1] == 6
assert scalar == bytes([128, 1, 4, 0, 0])

schema = pa.schema([pa.field("ordinal", pa.int32(), nullable=False),
                    pa.field("payload", pa.binary(), nullable=True)])
groups = [([10, -1], [b"", None]), ([], []), ([20], [b"\xff\x00"])]
sink = pa.BufferOutputStream()
with pq.ParquetWriter(sink, schema, version="2.6", data_page_version="2.0",
                      column_encoding={"ordinal": "PLAIN", "payload": "DELTA_LENGTH_BYTE_ARRAY"},
                      compression="NONE", use_dictionary=False, write_statistics=False,
                      store_schema=False) as writer:
    for integers, binary in groups:
        writer.write_table(pa.Table.from_arrays([pa.array(integers, pa.int32()), pa.array(binary, pa.binary())],
                                               schema=schema))
wire = sink.getvalue().to_pybytes()
size, = struct.unpack_from("<I", wire, len(wire) - 8)
start = len(wire) - 8 - size

# Give the empty chunks explicit spans while preserving footer group order.
pages = []
for tag, payload in [(0, b""), (6, scalar)]:
    fields = {index: (TType.I32, 0) for index in range(1, 7)}
    fields[4] = TType.I32, tag
    fields[7] = TType.BOOL, False
    sizes = TType.I32, len(payload)
    pages.append(thrift["encode"]({1: (TType.I32, 3), 2: sizes, 3: sizes, 8: (TType.STRUCT, fields)}) + payload)

def attach(metadata):
    group = thrift["list_field"](metadata, 4)[1]
    assert group[3] == (TType.I64, 0)
    group[2] = group[6] = TType.I64, sum(map(len, pages))
    offset = start
    for ordinal, (tag, page) in enumerate(zip((0, 6), pages, strict=True)):
        column = thrift["column_metadata"](metadata, group=1, column=ordinal)
        assert column[5] == column[7] == column[9] == (TType.I64, 0)
        column[2] = TType.LIST, (TType.I32, [3, tag])
        column[6] = column[7] = TType.I64, len(page)
        column[9] = TType.I64, offset
        offset += len(page)

framed = thrift["rewrite_footer"](wire[:start] + b"".join(pages) + wire[start:], attach)
for fixture in (wire, framed):
    with pq.ParquetFile(pa.BufferReader(fixture)) as file:
        assert file.schema_arrow == schema and file.num_row_groups == 3
        for index, (integers, binary) in enumerate(groups):
            projected = file.read_row_group(index)
            assert projected["ordinal"].to_pylist() == integers
            assert projected["payload"].to_pylist() == binary
digest = sha256(framed).hexdigest()
assert digest == "095df3ed224578be417cfec6a8acb3dc6f669a24c13f3b565552243018ca1e8e"
with pq.ParquetFile(pa.BufferReader(framed)) as file:
    last = file.metadata.row_group(2).column(1)
transport = TMemoryBuffer(framed[last.data_page_offset:])
last_header = thrift["read_struct"](TCompactProtocol(transport))
assert last_header[8][1][4] == (TType.I32, 6)
last_tag = last.data_page_offset + 14
assert framed[last_tag] == 12
damaged = framed[:last_tag] + bytes([6]) + framed[last_tag + 1:]
transport = TMemoryBuffer(damaged[last.data_page_offset:])
assert thrift["read_struct"](TCompactProtocol(transport))[8][1][4] == (TType.I32, 3)
print(f"Late tag control: group 2, column 1, page 0, header {last.data_page_offset}, tag byte {last_tag}")
target = Path(sys.argv[1])
target.write_bytes(framed)
print(digest, target.name, "PyArrow verified [2, 0, 1]")
