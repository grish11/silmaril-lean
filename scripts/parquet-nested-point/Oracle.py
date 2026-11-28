"""Observe the pinned nested pair and verify the file-derived negative controls."""

from hashlib import sha256
from io import BytesIO
from pathlib import Path
import runpy

scripts = Path(__file__).resolve().parents[1]
presence = runpy.run_path(str(scripts / "parquet-nested-presence" / "Oracle.py"))
source = presence["source"]
parse, page, footer = presence["parse"], presence["page"], presence["footer"]
pq = presence["oracle"]["pq"]
rows = pq.ParquetFile(BytesIO(source)).read(use_threads=False).column("point").to_pylist()
assert rows == [{"signed": -7, "wide": 4398046511104}, None, {"signed": 0, "wide": None}]
print(f"paired rows {rows}")

for label, replacement, levels in (("parent mismatch", 0x06, [2, 1, 0]),
                                    ("surplus INT64", 0x11, [1, 0, 1]),
                                    ("impossible level", 0x13, [3, 0, 1])):
    assert source[57] == 0x12
    altered = source[:57] + bytes([replacement]) + source[58:]
    assert parse(altered[35:67], page) == parse(source[35:67], page)
    assert altered[59:67] == source[59:67]
    observed = [(altered[57] >> (2 * row)) & 3 for row in range(3)]
    assert observed == levels
    print(f"{label}: levels {observed}, original scalar suffix {altered[59:67].hex()}, "
          f"SHA-256 {sha256(altered).hexdigest()}")

assert source[325] == 0
altered = source[:325] + bytes([2]) + source[326:]
parsed, extent = parse(altered[150:-8], footer)
[first, second] = parsed[4][0][1]
assert extent == 664 and first[3][4] == 0 and second[3][4] == 1
assert altered[4:67] == source[4:67]
print(f"wrong codec: chunk codecs {[first[3][4], second[3][4]]}, SHA-256 {sha256(altered).hexdigest()}")
