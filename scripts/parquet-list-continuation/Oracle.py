"""Reproduce native multi-page V1 files and a spec-authored continuation."""

from hashlib import sha256
from io import BytesIO
from pathlib import Path
import runpy
import struct
import sys

o = runpy.run_path(str(Path(__file__).resolve().parents[1] / "parquet-list-file" / "Oracle.py"))
pa, pq = o["pa"], o["pq"]
parse, record, items = o["parse"], o["record"], o["items"]
page, i32, i64 = o["page"], o["i32"], o["i64"]
chunk = record({**o["column"][1], 4: i64, 5: i32})
footer = {**o["footer"], 4: items(record({1: items(chunk), 3: i64}))}
ROWS = [None, [], [11, None], [22, None]]
CONTINUED = [None, [], [11, None, 22, None]]


def metadata(source):
    stop = len(source) - 8
    start = stop - struct.unpack_from("<I", source, stop)[0]
    result, consumed = parse(source[start:stop], footer)
    assert consumed == stop - start
    return start, result


def read(source):
    return pq.ParquetFile(BytesIO(source)).read(use_threads=False)["items"].to_pylist()


def write(path, indexed):
    values = pa.array(ROWS, type=pa.list_(pa.field("element", pa.int32(), nullable=True)))
    pq.write_table(pa.table({"items": values}), path, compression="NONE",
                   use_dictionary=False, use_compliant_nested_type=True,
                   write_statistics=False, data_page_version="1.0", write_page_index=indexed,
                   write_batch_size=1, max_rows_per_page=1, data_page_size=1)
    return path.read_bytes()


def section(source, cursor, width, count):
    length = struct.unpack_from("<I", source, cursor)[0]
    start = cursor + 4
    encoded = source[start:start + length]
    # The fixtures use one two-byte RLE singleton or one packed group.
    if encoded[0] == 2:
        assert length == 2 and count == 1
        result = [encoded[1]]
    else:
        assert encoded[0] == 3 and length == width + 1
        word = int.from_bytes(encoded[1:], "little")
        result = [(word >> (width * i)) & ((1 << width) - 1) for i in range(count)]
    return result, start + length, start + 1


def inspect(source, indexed, reps, rows):
    footer_start, meta = metadata(source)
    assert meta[2] == [{3: 0, 4: b"schema", 5: 1},
                       {3: 1, 4: b"items", 5: 1, 6: 3, 10: {3: {}}},
                       {3: 2, 4: b"list", 5: 1}, {1: 1, 3: 1, 4: b"element"}]
    [group] = meta[4]
    [col] = group[1]
    data = col[3]
    assert data[1] == 1 and data[3] == [b"items", b"list", b"element"] and data[4] == 0
    assert (4 in col and 5 in col) == indexed
    index_extent = f"[{col[4]}, {col[4] + col[5]})" if indexed else "absent"
    assert meta[3] == group[3] == len(rows)
    assert read(source) == rows
    print(f"footer @{footer_start}, OffsetIndex {index_extent}, rows {meta[3]}, slots {data[5]}")
    assert data[9] == 4
    cursor, stop = data[9], data[9] + data[7]
    slots, offsets = 0, []
    for rep, defs, words in zip(reps, [[0], [1], [3, 2], [3, 2]], [[], [], [11], [22]], strict=True):
        header, length = parse(source[cursor:stop], page)
        assert header == {1: 0, 2: header[3], 3: header[3], 5: {1: len(rep), 2: 0, 3: 3, 4: 3}}
        payload = cursor + length
        end = payload + header[3]
        actual_rep, definition, rep_value = section(source, payload, 1, len(rep))
        actual_defs, scalar, def_value = section(source, definition, 2, len(defs))
        assert actual_rep == rep and actual_defs == defs
        assert [entry[0] for entry in struct.iter_unpack("<i", source[scalar:end])] == words
        print(f"frame [{cursor}, {end}), rep value @{rep_value} {rep}, def value @{def_value} {defs}, PLAIN {words}")
        offsets.append((cursor, rep_value, def_value))
        slots += len(rep)
        cursor = end
    assert cursor == stop <= footer_start and slots == data[5] == 6
    print(f"PyArrow rows {rows}")
    return footer_start, meta, offsets


def describe(label, source):
    print(f"{label}: SHA-256 {sha256(source).hexdigest()}")


def change_footer_counts(source, start, meta, desired):
    """Replace exactly the two row count payloads, identified by Thrift."""
    result = bytearray(source)
    offsets = []
    for at in range(start, len(source) - 9):
        if source[at:at + 2] != bytes([0x16, 8]):
            continue
        trial = bytearray(source)
        trial[at + 1] = desired * 2
        _, changed = metadata(trial)
        if changed[3] != meta[3] or changed[4][0][3] != meta[4][0][3]:
            result[at + 1] = desired * 2
            offsets.append(at + 1)
    assert len(offsets) == 2
    return result, offsets


def main(directory):
    assert pa.__version__ == "26.0.1"
    reps = [[0], [0], [0, 1], [0, 1]]
    native = write(directory / "native-v1.parquet", indexed=False)
    describe("native-v1.parquet", native)
    start, meta, pages = inspect(native, False, reps, ROWS)

    authored, offsets = change_footer_counts(native, start, meta, len(CONTINUED))
    authored[pages[3][1]] = 3
    authored = bytes(authored)
    (directory / "authored-continuation-v1.parquet").write_bytes(authored)
    describe(f"authored-continuation-v1.parquet, row count payloads {offsets}", authored)
    inspect(authored, False, reps[:3] + [[1, 1]], CONTINUED)

    indexed = write(directory / "native-indexed-v1.parquet", indexed=True)
    describe("native-indexed-v1.parquet", indexed)
    _, _, indexed_pages = inspect(indexed, True, reps, ROWS)

    early = bytearray(native)
    early[pages[0][1]], early[pages[0][2]] = 1, 2
    describe("group-boundary continuation", early)
    after_empty = bytearray(native)
    after_empty[pages[2][1]] = 3
    describe("continuation after empty list", after_empty)
    wrong_rows = bytearray(native)
    wrong_rows[pages[3][1]] = 3
    describe("wrong row total", wrong_rows)
    indexed_continuation = bytearray(indexed)
    indexed_continuation[indexed_pages[3][1]] = 3
    describe("indexed continuation", indexed_continuation)

    count_marker = bytes.fromhex("15 00 16 0c 16 8c 02")
    assert native.count(count_marker, start) == 1
    count_at = native.index(count_marker, start) + 3
    for total in (5, 7):
        modified = bytearray(native)
        modified[count_at] = 2 * total
        _, wrong_slots = metadata(modified)
        assert wrong_slots[4][0][1][0][3][5] == total
        describe(f"wrong chunk slot count @{count_at} = {total}", modified)


if __name__ == "__main__":
    main(Path(sys.argv[1]))
