"""Reproduce native LIST files and inspect their original footer and V1 frames."""

from hashlib import sha256
from pathlib import Path
import runpy
import struct
import sys

o = runpy.run_path(str(Path(__file__).resolve().parents[1] / "parquet-list-v1" / "Oracle.py"))
pa, pq = o["pa"], o["pq"]
parse, record, items = o["parse"], o["record"], o["items"]
i32, i64, binary = o["i32"], o["i64"], o["binary"]
column = record({3: record({1: i32, 3: items(binary), 4: i32, 5: i64, 6: i64, 7: i64, 9: i64})})
schema = record({**o["schema"][1], 10: record({3: record({}), 4: record({})})})
footer = {2: items(schema), 3: i64, 4: items(record({1: items(column), 3: i64}))}
page, unpack = o["page"], o["unpack"]

ROWS = [
    [None, [], [None], [-7, None, 0], [9, None]],
    [[10, None], None, [], [None, -(1 << 31)], [(1 << 31) - 1, None]],
]
STEMS = ("nullable-int32-v1", "nullable-int32-v1-snappy")


def read_footer(source):
    size = struct.unpack_from("<I", source, len(source) - 8)[0]
    stop = len(source) - 8
    start = stop - size
    metadata, consumed = parse(source[start:stop], footer)
    assert consumed == size
    return metadata, start


def expected_wire(rows):
    reps, defs, values = [], [], []
    for row in rows:
        if not row:
            reps.append(0)
            defs.append(0 if row is None else 1)
            continue
        for ordinal, item in enumerate(row):
            reps.append(int(ordinal != 0))
            defs.append(2 if item is None else 3)
            if item is not None:
                values.append(item)
    return reps, defs, values


def produce(directory, stem, codec):
    path = directory / (stem + ".parquet")
    values = pa.array([row for group in ROWS for row in group],
                      type=pa.list_(pa.field("element", pa.int32(), nullable=True)))
    pq.write_table(pa.table({"samples": values}), path, compression=codec,
                   use_dictionary=False, use_compliant_nested_type=True,
                   row_group_size=5, data_page_version="1.0", write_statistics=False)
    parquet = pq.ParquetFile(path)
    assert parquet.num_row_groups == len(ROWS)
    assert [parquet.read_row_group(i, use_threads=False)[0].to_pylist()
            for i in range(len(ROWS))] == ROWS
    source = path.read_bytes()
    metadata, footer_start = read_footer(source)
    assert metadata[2] == [{3: 0, 4: b"schema", 5: 1},
                           {3: 1, 4: b"samples", 5: 1, 6: 3, 10: {3: {}}},
                           {3: 2, 4: b"list", 5: 1},
                           {1: 1, 3: 1, 4: b"element"}]
    assert metadata[3] == sum(map(len, ROWS))
    print(f"{path.name} PyArrow {pa.__version__} SHA-256 {sha256(source).hexdigest()}")
    print(f"footer [{footer_start}, {len(source) - 8}), LIST schema ordinal 1, element ordinal 3, column ordinal 0")
    first_stop = 4
    for index, (group, expected) in enumerate(zip(metadata[4], ROWS, strict=True)):
        [chunk] = group[1]
        col = chunk[3]
        start, stop = col[9], col[9] + col[7]
        header, used = parse(source[start:stop], page)
        body = start + used
        assert start == first_stop and stop <= footer_start and group[3] == len(expected)
        first_stop = stop
        assert col[1] == 1 and col[3] == [b"samples", b"list", b"element"]
        assert col[4] == (0 if codec == "NONE" else 1)
        assert header == {1: 0, 2: col[6] - used, 3: stop - body, 5: {1: col[5], 2: 0, 3: 3, 4: 3}}
        print(f"group {index}: rows {group[3]}, slots {col[5]}, codec {col[4]}, frame [{start}, {stop}), body @{body}")
        if codec != "NONE":
            continue
        rep_at = body + 4
        def_word = rep_at + struct.unpack_from("<I", source, body)[0]
        def_at = def_word + 4
        scalar_at = def_at + struct.unpack_from("<I", source, def_word)[0]
        reps = unpack(source[rep_at:def_word], 1)
        defs = unpack(source[def_at:scalar_at], 2)
        values = [word[0] for word in struct.iter_unpack("<i", source[scalar_at:stop])]
        assert (reps, defs, values) == expected_wire(expected)
        print(f"  repetition @{rep_at}: {reps}, definition @{def_at}: {defs}, PLAIN @{scalar_at}: {values}")
        print(f"  observed {expected}")
        if index == 1:
            assert source[rep_at + 1] & 1 == 0 and defs[0] == 3
            corrupt = bytearray(source)
            corrupt[rep_at + 1] |= 1
            assert read_footer(corrupt) == (metadata, footer_start)
            assert parse(corrupt[start:stop], page) == (header, used)
            assert unpack(corrupt[rep_at:def_word], 1) == [1] + reps[1:]
            assert corrupt[def_word:stop] == source[def_word:stop]
            print(f"  late continuation @{rep_at + 1}: byte 0x{corrupt[rep_at + 1]:02x}, SHA-256 {sha256(corrupt).hexdigest()}")

            assert source[start + 8] == 16
            corrupt_slots = source[:start + 8] + bytes([18]) + source[start + 9:]
            changed_header, consumed = parse(corrupt_slots[start:stop], page)
            assert consumed == used and changed_header[5][1] == 9
            assert read_footer(corrupt_slots) == (metadata, footer_start)
            assert corrupt_slots[body:stop] == source[body:stop]
            print(f"  late slot count @{start + 8}: 9 vs 8, SHA-256 {sha256(corrupt_slots).hexdigest()}")

    if codec == "NONE":
        marker = bytes.fromhex("15 06 4c 3c 00 00")
        assert source.count(marker, footer_start) == 1
        at = source.index(marker, footer_start)
        corrupt = bytearray(source)
        corrupt[at + 3] = 0x4C
        changed, _ = read_footer(corrupt)
        assert changed[2][1].pop(10) == {4: {}}
        assert changed[2][1] == {key: value for key, value in metadata[2][1].items() if key != 10}
        changed[2][1][10] = {3: {}}
        assert changed == metadata
        print(f"wrong logical arm @{at + 3}: byte 0x4c, SHA-256 {sha256(corrupt).hexdigest()}")
        corrupt = bytearray(source)
        corrupt[at + 1] = 8
        changed, _ = read_footer(corrupt)
        assert changed[2][1][6] == 4
        changed[2][1][6] = 3
        assert changed == metadata
        print(f"wrong converted code @{at + 1}: 4 vs 3, SHA-256 {sha256(corrupt).hexdigest()}")

        repeated = bytes.fromhex("07") + b"samples" + bytes.fromhex("04") + b"list"
        pos = source.index(repeated, footer_start) + 2
        corrupt = bytearray(source)
        corrupt[pos] = ord("i")
        changed, _ = read_footer(corrupt)
        assert changed[4][0][1][0][3][3] == [b"simples", b"list", b"element"]
        changed[4][0][1][0][3][3][0] = b"samples"
        assert changed == metadata
        print(f"wrong chunk path @{pos}: simples/list/element, SHA-256 {sha256(corrupt).hexdigest()}")


if __name__ == "__main__":
    output = Path(sys.argv[1])
    produce(output, STEMS[0], "NONE")
    produce(output, STEMS[1], "SNAPPY")
