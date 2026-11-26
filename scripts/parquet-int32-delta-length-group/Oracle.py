"""Generate and check PLAIN INT32 / DELTA_LENGTH_BYTE_ARRAY projection fixtures."""
from hashlib import sha256
from importlib.metadata import version as pin
from pathlib import Path
from runpy import run_path
import sys

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

assert (pin("pyarrow"), pin("thrift")) == ("26.0.1", "0.25.0")
root = Path(__file__).resolve().parents[2]
header_fields = run_path(str(root / "scripts/parquet-scalar-page/PyArrowOracle.py"))["header_fields"]
thrift = run_path(str(root / "tests/formats/parquet-timestamp-leaf/check-fixtures.py"))
output = Path(sys.argv[1])
output.mkdir(parents=True, exist_ok=True)
base = [b"", None, b"\xff\0\x80", b"x" * 48, None, None, None, None,
        b"\0", b"\xc3\xa9", None, b"y" * 36]
opaque = [value if value in (None, b"") else value + bytes([group]) for group in range(3) for value in base]
schema = pa.schema([pa.field("ordinal", pa.int32(), nullable=False),
                    pa.field("payload", pa.binary()), pa.field("decoy", pa.int64(), nullable=False)])
table = pa.Table.from_arrays([pa.array(range(36), pa.int32()), pa.array(opaque, pa.binary()),
                             pa.array(range(100, 136), pa.int64())], schema=schema)
def reject_selected(changed, name, header, changed_byte):
    with pq.ParquetFile(pa.BufferReader(changed)) as parquet:
        assert parquet.read_row_group(1, columns=["ordinal"])["ordinal"].to_pylist() == list(range(12, 24))
        for group in (0, 2):
            batch = parquet.read_row_group(group, columns=["payload"])
            assert batch["payload"].to_pylist() == opaque[group * 12:(group + 1) * 12]
        try:
            parquet.read_row_group(1, columns=["payload"])
        except (OSError, pa.ArrowInvalid, pa.ArrowNotImplementedError) as reason:
            print(name, sha256(changed).hexdigest(), "group 1 column 1 page 2 header", header,
                  "changed byte", changed_byte, repr(reason))
        else:
            raise AssertionError("PyArrow accepted the damaged selected page")
    (output / name).write_bytes(changed)


def damage_v2(wire):
    header = 760
    transport = TMemoryBuffer(wire[header:])
    fields = thrift["read_struct"](TCompactProtocol(transport))
    size = transport.cstringio_buf.tell()
    fields_v2 = fields[8][1]
    assert fields_v2[4] == (TType.I32, 6)
    scalar = header + size + fields_v2[5][1]
    # The first three header ULEBs are 128, 4 and 3; the fourth is
    # the zigzag code of the first length (2). Increase all lengths by one.
    assert wire[scalar:scalar + 5] == bytes([128, 1, 4, 3, 4])
    changed_length = wire[:scalar + 4] + bytes([6]) + wire[scalar + 5:]
    reject_selected(changed_length, "plain-int32-delta-length-v2-bad-length.parquet", header, scalar + 4)
    fields_v2[4] = TType.I32, 3
    replacement = thrift["encode"](fields)
    assert len(replacement) == size
    differences = [i for i, (left, right) in enumerate(zip(wire[header:header + size], replacement, strict=True))
                   if left != right]
    assert len(differences) == 1
    reject_selected(wire[:header] + replacement + wire[header + size:],
                    "plain-int32-delta-length-v2-bad-tag.parquet", header, header + differences[0])


for version in (1, 2):
    path = output / f"plain-int32-delta-length-v{version}.parquet"
    pq.write_table(table, path, version="2.6", data_page_version=f"{version}.0",
                   use_dictionary=False, compression="NONE", write_statistics=False,
                   row_group_size=12, data_page_size=32, write_batch_size=4, write_page_checksum=False,
                   column_encoding={"ordinal": "PLAIN", "payload": "DELTA_LENGTH_BYTE_ARRAY", "decoy": "PLAIN"})
    wire = path.read_bytes()
    print(path.name, sha256(wire).hexdigest())
    with pq.ParquetFile(path) as parquet:
        assert parquet.schema.column(0).physical_type == "INT32"
        assert parquet.schema.column(1).physical_type == "BYTE_ARRAY"
        assert parquet.schema.column(0).max_definition_level == 0
        assert parquet.schema.column(1).max_definition_level == 1
        for group in range(3):
            expected = slice(12*group, 12*(group+1))
            selected = parquet.read_row_group(group, columns=["ordinal", "payload"])
            assert selected["ordinal"].to_pylist() == list(range(36))[expected]
            assert selected["payload"].to_pylist() == opaque[expected]
            columns = parquet.metadata.row_group(group)
            for ordinal, tag in ((0, 0), (1, 6)):
                column = columns.column(ordinal)
                assert column.compression == "UNCOMPRESSED" and not column.has_dictionary_page
                value_encoding = "PLAIN" if ordinal == 0 else "DELTA_LENGTH_BYTE_ARRAY"
                assert set(column.encodings) == {"RLE", value_encoding}
                cursor = column.data_page_offset
                stop = cursor + column.total_compressed_size
                frames = []
                while cursor < stop:
                    transport = TMemoryBuffer(wire[cursor:stop])
                    header = header_fields(TCompactProtocol(transport), (5, 8))
                    body = cursor + transport.cstringio_buf.tell()
                    end = body + header[3]
                    assert cursor < body <= end <= stop
                    info = header[5 if version == 1 else 8]
                    assert info[2 if version == 1 else 4] == tag
                    assert 4 not in header and header[2] == header[3]
                    if version == 1:
                        assert [info[3], info[4]] == [3, 3]
                    else:
                        assert [info[3], info[6], info[7]] == [info[1], 0, False]
                        first = 12 * group + sum(count for _, count in frames)
                        nulls = opaque[first:first + info[1]].count(None) if ordinal == 1 else 0
                        assert info[2] == nulls
                    frames.append((cursor, info[1]))
                    cursor = end
                assert cursor == stop
                assert [count for _, count in frames] == ([8, 4] if ordinal == 0 else [4, 4, 4])
                print(f"  group {group}, col {ordinal}, tag {tag}, (header, rows) {frames}")
    if version == 2:
        damage_v2(wire)
