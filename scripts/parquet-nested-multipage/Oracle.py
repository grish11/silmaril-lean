"""Pin the unequal V1 sibling page cuts and decode their original levels."""

from hashlib import sha256
from io import BytesIO
from pathlib import Path
import runpy
import struct
import sys

o = runpy.run_path(str(Path(__file__).resolve().parents[1] / "parquet-column-index" / "Oracle.py"))
pa, pq = o["pa"], o["pq"]
parse, record, items = o["parse"], o["record"], o["items"]
i32, i64 = o["I32"], o["I64"]
footer = {4: items(record({1: items(record({3: record({4: i32, 7: i64, 9: i64})}))}))}
page = {1: i32, 2: i32, 3: i32, 4: i32, 5: record({i: i32 for i in range(1, 5)})}
schema = pa.struct([pa.field("signed", pa.int32(), nullable=False), pa.field("wide", pa.int64())])
rows = [None if i % 7 == 2 else {"signed": -100 + i, "wide": None if i % 5 == 3 else (1 << 42) + i}
        for i in range(12)]


def read_leaf(source, metadata, field, width, code):
    assert metadata[4] == 0
    cursor, size = metadata[9], metadata[7]
    end = cursor + size
    cut = 0
    observed = []
    while cursor < end:
        header, used = parse(source[cursor:end], page)
        body = cursor + used
        count, encoding, definitions, repetitions = [header[5][i] for i in range(1, 5)]
        assert header[1] == 0 and header[2] == header[3] and 4 not in header
        assert (encoding, definitions, repetitions) == (0, 3, 3)
        stop = body + header[3]
        length = struct.unpack_from("<I", source, body)[0]
        section = source[body + 4:body + 4 + length]
        suffix = source[body + 4 + length:stop]
        if section[0] == 3:
            assert len(section) == 1 + width and count <= 8
            word = int.from_bytes(section[1:], "little")
            levels = [(word >> (width * i)) & ((1 << width) - 1) for i in range(count)]
        else:
            assert section[0] == 2 * count and len(section) == 2 and section[1] < 1 << width
            levels = [section[1]] * count
        segment = rows[cut:cut + count]
        expected = [0 if row is None else 1 if row[field] is None else width for row in segment]
        assert levels == expected
        values = [row[field] for row in segment if row is not None and row[field] is not None]
        assert suffix == struct.pack(f"<{len(values)}{code}", *values)
        print(f"{field} rows [{cut}, {cut + count}) frame [{cursor}, {stop}) payload @{body} "
              f"levels {levels} scalar bytes {len(suffix)}")
        observed.append((cursor, body, stop, count, levels))
        cut += count
        cursor = stop
    assert cursor == end and cut == len(rows)
    return observed


def write(path):
    table = pa.table({"point": pa.array(rows, type=schema)})
    pq.write_table(table, path, compression="NONE", use_dictionary=False, data_page_version="1.0",
                   data_page_size=16, write_batch_size=2, write_page_index=True)
    source = path.read_bytes()
    assert sha256(source).hexdigest() == "cb5b8ede855189f8ff69a3437ba2adfda76f6bfc8614bae17ff71f33b2849bbc"
    assert pq.ParquetFile(BytesIO(source)).read(use_threads=False).column("point").to_pylist() == rows
    footer_bytes = struct.unpack("<I", source[-8:-4])[0]
    metadata, consumed = parse(source[-8 - footer_bytes:-8], footer)
    assert consumed == footer_bytes
    [group] = metadata[4]
    print(f"PyArrow {pa.__version__} SHA-256 {sha256(source).hexdigest()}")
    left, right = [read_leaf(source, chunk[3], field, width, code)
                   for chunk, field, width, code in zip(group[1], ("signed", "wide"), (1, 2),
                                                        ("i", "q"), strict=True)]
    assert [x[3] for x in left] == [6, 6] and [x[3] for x in right] == [2, 4, 2, 4]
    start, body, stop, count, levels = right[-1]
    assert levels == [1, 0, 2, 2] and source[body + 5] == 0xA1
    mismatch = source[:body + 5] + b"\xa4" + source[body + 6:]
    assert parse(mismatch[start:stop], page) == parse(source[start:stop], page)
    assert mismatch[body + 7:stop] == source[body + 7:stop]
    observed = [(mismatch[body + 5] >> (2 * i)) & 3 for i in range(count)]
    assert observed == [0, 1, 2, 2]
    print(f"late mismatch byte {body + 5}, levels {observed}, SHA-256 {sha256(mismatch).hexdigest()}")
    short_scalar = source[:body + 5] + b"\xa2" + source[body + 6:]
    assert parse(short_scalar[start:stop], page) == parse(source[start:stop], page)
    assert short_scalar[body + 7:stop] == source[body + 7:stop]
    observed = [(short_scalar[body + 5] >> (2 * i)) & 3 for i in range(count)]
    assert observed == [2, 0, 2, 2] and stop - body - 7 == 16
    print(f"short scalar page byte {body + 5}, levels {observed}, 16 original bytes for 3 INT64s, "
          f"SHA-256 {sha256(short_scalar).hexdigest()}")
    assert source[start + 8] == 8
    wrong_total = source[:start + 8] + bytes([6]) + source[start + 9:]
    header, used = parse(wrong_total[start:stop], page)
    assert used == body - start and header[5][1] == count - 1
    print(f"wrong total byte {start + 8}, 11 advertised right slots, SHA-256 {sha256(wrong_total).hexdigest()}")


if __name__ == "__main__":
    write(Path(sys.argv[1]))
