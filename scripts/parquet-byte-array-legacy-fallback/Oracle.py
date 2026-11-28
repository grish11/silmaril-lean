"""Pin the actual parquet-java V1 fallback and reject a damaged late PLAIN value."""
from hashlib import sha256
from importlib.metadata import version
from pathlib import Path
from runpy import run_path
import struct
import sys

import pyarrow.parquet as pq
from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

assert (version("pyarrow"), version("thrift")) == ("26.0.1", "0.25.0")
thrift = run_path("tests/formats/parquet-timestamp-leaf/check-fixtures.py")
directory = Path(sys.argv[1])
input_path = directory / "java-binary-fallback-v1.parquet"
wire = input_path.read_bytes()
expected = [
    None if i % 13 == 5 else (b"repeat-a" if i % 2 == 0 else b"repeat-b") if i < 256 else
    f"distinct-{i:04d}-".encode("ascii") + b"opaque-value-" * 4
    for i in range(384)
]


def inspect(path):
    with pq.ParquetFile(path) as file:
        assert file.metadata.created_by == (
            "parquet-mr version 1.16.0 (build 402c3810c372d29603e181771acebfecc71bef61)"
        )
        assert file.num_row_groups == 1
        leaf = file.schema.column(1)
        assert (leaf.name, leaf.physical_type, leaf.max_definition_level, leaf.max_repetition_level) == (
            "payload", "BYTE_ARRAY", 1, 0
        )
        row = file.read_row_group(0, use_threads=False)
        assert row["ordinal"].to_pylist() == list(range(384)) and row["payload"].to_pylist() == expected
        chunk = file.metadata.row_group(0).column(1)
        assert chunk.compression == "UNCOMPRESSED"
        assert (chunk.dictionary_page_offset, chunk.data_page_offset) == (1900, 1937)
        assert set(chunk.encodings) == {"PLAIN", "RLE", "BIT_PACKED", "PLAIN_DICTIONARY"}
        return chunk.dictionary_page_offset + chunk.total_compressed_size


def canonicalize(metadata):
    # parquet-java writes the encoding set in JVM-dependent order.
    # Canonicalize only that footer list. Original pages and offsets are untouched.
    for index in range(2):
        chunk = thrift["column_metadata"](metadata, group=0, column=index)
        tag, (item, encodings) = chunk[2]
        assert tag == TType.LIST and item == TType.I32
        chunk[2] = tag, (item, sorted(encodings))


stop = inspect(input_path)
canonical = thrift["rewrite_footer"](wire, canonicalize)
footer_size, = struct.unpack_from("<I", wire, len(wire) - 8)
footer_start = len(wire) - 8 - footer_size
assert canonical[:footer_start] == wire[:footer_start]
clean = directory / "parquet-java-v1-legacy-fallback.parquet"
clean.write_bytes(canonical)
assert inspect(clean) == stop

memory = TMemoryBuffer(canonical[1900:stop])
protocol = TCompactProtocol(memory)
dictionary = thrift["read_struct"](protocol)
assert dictionary[1][1] == 2 and dictionary[7][1][1][1] == dictionary[7][1][2][1] == 2
assert 4 not in dictionary and dictionary[2] == dictionary[3]
assert memory.readAll(dictionary[3][1]) == b"\x08\0\0\0repeat-a\x08\0\0\0repeat-b"
tags = []
rows = 0
while 1900 + memory.cstringio_buf.tell() < stop:
    header = 1900 + memory.cstringio_buf.tell()
    fields = thrift["read_struct"](protocol)
    body = 1900 + memory.cstringio_buf.tell()
    assert fields[1][1] == 0 and 4 not in fields and fields[2] == fields[3]
    info = fields[5][1]
    assert info[3][1] == 3 and info[4][1] == 4
    rows += info[1][1]
    tags.append(info[2][1])
    memory.readAll(fields[3][1])
assert tags == [2] * 10 + [0] * 9 and rows == 384 and 1900 + memory.cstringio_buf.tell() == stop
assert (header, body) == (10089, 10108)
definition_size, = struct.unpack_from("<I", canonical, body)
length_offset = body + 4 + definition_size
length, = struct.unpack_from("<I", canonical, length_offset)
assert 0 < length < stop - length_offset - 4
damaged = directory / "parquet-java-v1-legacy-fallback-bad-length.parquet"
damaged.write_bytes(canonical[:length_offset] + struct.pack("<i", -1) + canonical[length_offset + 4:])
with pq.ParquetFile(damaged) as file:
    try:
        file.read_row_group(0, columns=["payload"], use_threads=False)
    except (OSError, ValueError):
        pass
    else:
        raise AssertionError("PyArrow admitted the damaged final PLAIN page")
for path in (clean, damaged):
    print(f"{sha256(path.read_bytes()).hexdigest()}  {path.name}")
print(f"V1: dictionary tag 2, data tags 2 × 10 then 0 × 9, RLE definitions, absent BIT_PACKED repetition")
print(f"Final PLAIN frame 19, header {header}, length word {length_offset}")
