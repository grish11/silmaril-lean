"""Read the pinned PyArrow nested file's definition bits independently with Thrift."""

from hashlib import sha256
from io import BytesIO
from pathlib import Path
import runpy
import struct

scripts = Path(__file__).resolve().parents[1]
oracle = runpy.run_path(str(scripts / "parquet-column-index" / "Oracle.py"))
parse, record, items = oracle["parse"], oracle["record"], oracle["items"]
I32, I64 = oracle["I32"], oracle["I64"]
chunk = record({3: record({4: I32, 7: I64, 9: I64})})
footer = {4: items(record({1: items(chunk)}))}
page = {1: I32, 2: I32, 3: I32, 4: I32, 5: record({i: I32 for i in range(1, 5)})}

source = Path("data/parquet-nested-footer/optional-point.parquet").read_bytes()
assert sha256(source).hexdigest() == "fa0408e5c83e3cd1b37c5cb25d55e71cf951112fe746ab8ee1389e8325475c60"
footer_bytes = struct.unpack("<I", source[-8:-4])[0]
metadata, consumed = parse(source[-8 - footer_bytes:-8], footer)
assert consumed == footer_bytes
[group] = metadata[4]
rows = oracle["pq"].ParquetFile(BytesIO(source)).read(use_threads=False).column("point").to_pylist()
assert rows == [{"signed": -7, "wide": 1 << 42}, None, {"signed": 0, "wide": None}]

for field, raw, width, code in zip(("signed", "wide"), group[1], (1, 2), ("i", "q"), strict=True):
    meta = raw[3]
    start, size = meta[9], meta[7]
    assert meta[4] == 0
    header, header_size = parse(source[start:start + size], page)
    assert header == {1: 0, 2: size - header_size, 3: size - header_size, 5: {1: 3, 2: 0, 3: 3, 4: 3}}
    body_start = start + header_size
    length = struct.unpack_from("<I", source, body_start)[0]
    definitions = source[body_start + 4:body_start + 4 + length]
    values = source[body_start + 4 + length:start + size]
    # This producer emits exactly one bit-packed group of eight levels.
    # The first byte is the hybrid run header (one group, bit-packed).
    assert definitions[0] == 3 and len(definitions) == 1 + width
    word = int.from_bytes(definitions[1:], "little")
    levels = [(word >> (width * slot)) & ((1 << width) - 1) for slot in range(3)]
    expected = [0 if row is None else 1 if row[field] is None else width for row in rows]
    assert levels == expected
    visible = [row[field] for row in rows if row is not None and row[field] is not None]
    assert values == struct.pack(f"<{len(visible)}{code}", *visible)
    print(f"{field}: header [{start}, {body_start}), payload [{body_start}, {start + size})")
    print(f"  definitions {definitions.hex(' ')} levels {levels}; scalar suffix {values.hex(' ')} values {visible}")
