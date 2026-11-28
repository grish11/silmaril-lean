"""Produce canonical nullable LIST and check original V1 level bits with Thrift."""

from hashlib import sha256
from io import BytesIO
from pathlib import Path
import runpy
import struct
import sys

o = runpy.run_path(str(Path(__file__).resolve().parents[1] / "parquet-column-index" / "Oracle.py"))
pa, pq = o["pa"], o["pq"]
parse, record, items = o["parse"], o["record"], o["items"]
i32, i64, binary = o["I32"], o["I64"], o["BINARY"]
schema = record({1: i32, 3: i32, 4: binary, 5: i32, 6: i32, 10: record({3: record({})})})
column = record({3: record({1: i32, 3: items(binary), 4: i32, 5: i64, 7: i64, 9: i64})})
footer = {2: items(schema), 4: items(record({1: items(column), 3: i64}))}
page = {1: i32, 2: i32, 3: i32, 4: i32, 5: record({i: i32 for i in range(1, 5)})}
rows = [None, [], [None], [-7, None, 0], [9, None]]


def unpack(section, width):
    assert len(section) == width + 1 and section[0] == 3
    word = int.from_bytes(section[1:], "little")
    return [(word >> (width * i)) & ((1 << width) - 1) for i in range(8)]


def write(path):
    values = pa.array(rows, type=pa.list_(pa.field("element", pa.int32(), nullable=True)))
    pq.write_table(pa.table({"items": values}), path, compression="NONE", use_dictionary=False,
                   use_compliant_nested_type=True, data_page_version="1.0", write_page_index=True)
    source = path.read_bytes()
    assert sha256(source).hexdigest() == "e54b974102a55ace9849e3b060fb77a967309c0999c59713ccf85410530c510e"
    observed = pq.ParquetFile(BytesIO(source)).read(use_threads=False).column("items").to_pylist()
    assert observed == rows
    footer_bytes = struct.unpack("<I", source[-8:-4])[0]
    footer_start = len(source) - 8 - footer_bytes
    metadata, consumed = parse(source[footer_start:-8], footer)
    assert consumed == footer_bytes
    assert metadata[2] == [{3: 0, 4: b"schema", 5: 1},
                           {3: 1, 4: b"items", 5: 1, 6: 3, 10: {3: {}}},
                           {3: 2, 4: b"list", 5: 1},
                           {1: 1, 3: 1, 4: b"element"}]
    [group] = metadata[4]
    [chunk] = group[1]
    meta = chunk[3]
    assert group[3] == 5 and meta[1] == 1 and meta[3] == [b"items", b"list", b"element"]
    assert meta[4] == 0 and meta[5] == 8
    start, stop = meta[9], meta[9] + meta[7]
    header, length = parse(source[start:stop], page)
    body = start + length
    assert header == {1: 0, 2: stop - body, 3: stop - body, 5: {1: 8, 2: 0, 3: 3, 4: 3}}
    rep_size = struct.unpack_from("<I", source, body)[0]
    rep_at = body + 4
    def_word = rep_at + rep_size
    def_size = struct.unpack_from("<I", source, def_word)[0]
    def_at = def_word + 4
    scalar_at = def_at + def_size
    repetitions = unpack(source[rep_at:def_word], 1)
    definitions = unpack(source[def_at:scalar_at], 2)
    assert repetitions == [0, 0, 0, 0, 1, 1, 0, 1]
    assert definitions == [0, 1, 2, 3, 2, 3, 3, 2]
    assert source[scalar_at:stop] == struct.pack("<iii", -7, 0, 9)

    print(f"PyArrow {pa.__version__} SHA-256 {sha256(source).hexdigest()}")
    print(f"footer [{footer_start}, {len(source) - 8}), canonical optional items / repeated list / optional INT32 element")
    print(f"group rows {group[3]}, chunk slots {meta[5]}, frame [{start}, {stop}), payload @{body}")
    print(f"repetition @{rep_at}: {source[rep_at:def_word].hex(' ')} -> {repetitions}")
    print(f"definition @{def_at}: {source[def_at:scalar_at].hex(' ')} -> {definitions}")
    print(f"PLAIN @{scalar_at}: {source[scalar_at:stop].hex(' ')}")
    print(f"rows {observed}")
    print(f"first repetition byte at {rep_at + 1}, first definition byte at {def_at + 1}")


    for label, rep, defn in [
        ("initial continuation", 0xB1, 0xE6),
        ("repeated empty marker", 0xB2, 0xE4),
        ("continuation after empty", 0xB4, 0xE4),
        ("surplus scalar", 0xB0, 0xA4),
    ]:
        altered = bytearray(source)
        altered[rep_at + 1] = rep
        altered[def_at + 1] = defn
        raw = bytes(altered)
        assert parse(raw[start:stop], page) == (header, length)
        assert raw[scalar_at:stop] == source[scalar_at:stop]
        changed_reps = unpack(raw[rep_at:def_word], 1)
        changed_defs = unpack(raw[def_at:scalar_at], 2)
        print(f"{label}: reps {changed_reps}, defs {changed_defs}, SHA-256 {sha256(raw).hexdigest()}")

    assert source[start + 8] == 16
    wrong_slots = source[:start + 8] + bytes([18]) + source[start + 9:]
    altered_header, used = parse(wrong_slots[start:stop], page)
    assert altered_header[5][1] == 9 and used == length
    assert wrong_slots[body:stop] == source[body:stop]
    print(f"wrong slot count: header advertises 9, SHA-256 {sha256(wrong_slots).hexdigest()}")


if __name__ == "__main__":
    write(Path(sys.argv[1]))
