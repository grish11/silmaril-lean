"""Reuse pinned parquet-java V1 frames around an explicitly framed zero-row group."""

from copy import deepcopy
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
pinned = root / "data/parquet-byte-array-legacy-fallback/parquet-java-v1-legacy-fallback.parquet"
original = pinned.read_bytes()
assert sha256(original).hexdigest() == "63231c6286d24acc8ff3fcbf72b0641fb861dd7a78eec9908899cc9b14c07135"
footer_size, = struct.unpack_from("<I", original, len(original) - 8)
memory = TMemoryBuffer(original[-8 - footer_size:-8])
metadata = thrift["read_struct"](TCompactProtocol(memory))
assert memory.cstringio_buf.tell() == footer_size
[group] = thrift["list_field"](metadata, 4)
assert group[3] == (TType.I64, 384)
first_data, last_data = 4, 10886
producer_pages = original[first_data:last_data]
i32, i64 = TType.I32, TType.I64


def relocate(delta, ordinal):
    result = deepcopy(group)
    result[5] = i64, first_data + delta
    result[7] = TType.I16, ordinal
    for column in thrift["list_field"](result, 1):
        for field in (4, 5, 6, 7):
            column.pop(field, None)  # Detached index sections are outside these copied chunks.
        chunk = column[3][1]
        for field in (9, 11):
            if field in chunk:
                chunk[field] = i64, chunk[field][1] + delta
    return result


def zero_page(body):
    size = i32, len(body)
    return thrift["encode"]({
        1: (i32, 0), 2: size, 3: size,
        5: (TType.STRUCT, {1: (i32, 0), 2: (i32, 0), 3: (i32, 3), 4: (i32, 4)}),
    }) + body


def empty_group():
    chunks = []
    columns = []
    offset = last_data
    for physical, name, body in [(1, "ordinal", b""), (6, "payload", bytes(4))]:
        page = zero_page(body)
        chunk = {
            1: (i32, physical), 2: (TType.LIST, (i32, [0, 3, 4])),
            3: (TType.LIST, (TType.STRING, [name.encode()])), 4: (i32, 0), 5: (i64, 0),
            6: (i64, len(page)), 7: (i64, len(page)), 9: (i64, offset),
        }
        chunks.append(page)
        columns.append({2: (i64, 0), 3: (TType.STRUCT, chunk)})
        offset += len(page)
    size = i64, offset - last_data
    return b"".join(chunks), {
        1: (TType.LIST, (TType.STRUCT, columns)), 2: size, 3: (i64, 0), 5: (i64, last_data),
        6: size, 7: (TType.I16, 1),
    }


empty_pages, empty = empty_group()
shift = len(producer_pages) + len(empty_pages)
metadata[3] = i64, 768
metadata[4] = TType.LIST, (TType.STRUCT, [relocate(0, 0), empty, relocate(shift, 2)])
footer = thrift["encode"](metadata)
clean = b"PAR1" + producer_pages + empty_pages + producer_pages + footer + struct.pack("<I", len(footer)) + b"PAR1"
assert clean[first_data:last_data] == clean[first_data + shift:last_data + shift] == producer_pages

header, length_offset = 10089 + shift, 10116 + shift
assert struct.unpack_from("<I", clean, length_offset)[0] == 66
damaged = clean[:length_offset] + b"\xff" * 4 + clean[length_offset + 4:]

with pq.ParquetFile(pa.BufferReader(original)) as file:
    reference = file.read_row_group(0).to_pydict()
for wire in (clean, damaged):
    with pq.ParquetFile(pa.BufferReader(wire)) as file:
        assert [file.metadata.row_group(i).num_rows for i in range(3)] == [384, 0, 384]
        assert file.read_row_group(0).to_pydict() == reference
        assert file.read_row_group(1).to_pydict() == {"ordinal": [], "payload": []}
        if wire == clean:
            assert file.read_row_group(2).to_pydict() == reference
        else:
            try:
                file.read_row_group(2, columns=["payload"])
            except (OSError, ValueError):
                pass
            else:
                raise AssertionError("PyArrow accepted the damaged last group")

out = Path(sys.argv[1])
out.mkdir(parents=True, exist_ok=True)
for label, wire in (("legacy-v1-empty-middle.parquet", clean), ("legacy-v1-late-error.parquet", damaged)):
    (out / label).write_bytes(wire)
    print(f"{sha256(wire).hexdigest()}  {label}")
print(f"PyArrow verified [384, 0, 384] and [384, 0] before damage at group 2, column 1, frame 19, header {header}")
