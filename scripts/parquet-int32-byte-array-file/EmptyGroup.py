"""Frame and verify an admitted empty group between two PyArrow groups."""

from hashlib import sha256
from importlib.metadata import version as package_version
from pathlib import Path
from runpy import run_path
import struct
import sys

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType

assert package_version("pyarrow") == "26.0.1"
assert package_version("thrift") == "0.25.0"
root = Path(__file__).resolve().parents[2]
thrift = run_path(str(root / "tests/formats/parquet-timestamp-leaf/check-fixtures.py"))
schema = pa.schema([
    pa.field("ordinal", pa.int32(), nullable=False),
    pa.field("payload", pa.binary()),
])
groups = [([-2**31, 0, 17], [None, b"", b"\xff\0"]),
          ([], []),
          ([2**31 - 1, -1], [b"\x80", b"xy"])]


def produce():
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, version="2.6", data_page_version="2.0",
                          compression="NONE", column_encoding="PLAIN", use_dictionary=False,
                          write_statistics=False, write_page_checksum=False, store_schema=False) as writer:
        for integers, binary in groups:
            writer.write_table(pa.Table.from_arrays([
                pa.array(integers, pa.int32()), pa.array(binary, pa.binary()),
            ], schema=schema))
    return sink.getvalue().to_pybytes()


def frame_empty_group(wire):
    # As in the timestamp fixture, the producer's zero-offset, zero-size
    # chunks need a real in-file span to exercise the unchanged checked reader.
    zero = TType.I32, 0
    page = thrift["encode"]({
        1: (TType.I32, 3), 2: zero, 3: zero,
        8: (TType.STRUCT, {**dict.fromkeys(range(1, 7), zero), 7: (TType.BOOL, False)}),
    })
    size, = struct.unpack_from("<I", wire, len(wire) - 8)
    start = len(wire) - 8 - size

    def attach(metadata):
        group = thrift["list_field"](metadata, 4)[1]
        assert group[3] == (TType.I64, 0)
        group[2] = group[6] = TType.I64, 2 * len(page)
        for ordinal in range(2):
            column = thrift["column_metadata"](metadata, group=1, column=ordinal)
            assert column[5] == column[7] == column[9] == (TType.I64, 0)
            assert column[2] == (TType.LIST, (TType.I32, [3]))
            column[2] = TType.LIST, (TType.I32, [3, 0])
            column[6] = column[7] = TType.I64, len(page)
            column[9] = TType.I64, start + ordinal * len(page)

    return thrift["rewrite_footer"](wire[:start] + page + page + wire[start:], attach)


unframed = produce()
wire = frame_empty_group(unframed)
for source in (unframed, wire):
    with pq.ParquetFile(pa.BufferReader(source)) as file:
        assert file.schema_arrow == schema and file.metadata.num_row_groups == 3
        for index, (integers, binary) in enumerate(groups):
            batch = file.read_row_group(index, use_threads=False)
            assert batch["ordinal"].to_pylist() == integers
            assert batch["payload"].to_pylist() == binary
path = Path(sys.argv[1])
path.write_bytes(wire)
print(f"{sha256(wire).hexdigest()}  {path.name}")
print("PyArrow verified [3, 0, 2] rows before and after the empty-chunk framing edit")
