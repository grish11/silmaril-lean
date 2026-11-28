"""Produce a two-leaf file and inspect original footer item intervals with Thrift."""

from hashlib import sha256
from io import BytesIO
from pathlib import Path
import runpy
import struct
import sys

oracle = runpy.run_path(
    str(Path(__file__).resolve().parents[1] / "parquet-column-index" / "Oracle.py"))
pa, pq = oracle["pa"], oracle["pq"]
parse, items, record = oracle["parse"], oracle["items"], oracle["record"]
i32, binary, boolean = oracle["I32"], oracle["BINARY"], oracle["BOOL"]
schema = {1: i32, 4: binary, 5: i32, 6: i32, 10: record({10: record({2: boolean})})}
order = record({index: record({}) for index in (1, 2, 3)})
footer_schema = {2: items(record(schema)), 7: items(order)}
SHA256 = "e429fed1f404dc10876d68b5a4785bd804279fae80e0836375e850ce986180b0"
ORDER_FIELD = bytes.fromhex("19 2c 1c 00 00 1c 00 00")


def item_extents(footer):
    transport = oracle["TMemoryBuffer"](footer)
    protocol = oracle["BinaryCompact"](transport)
    kind = oracle["TType"]
    tell = transport.cstringio_buf.tell
    result = []
    protocol.readStructBegin()
    while True:
        _, wire_type, tag = protocol.readFieldBegin()
        if wire_type == kind.STOP:
            break
        start = tell()
        if tag in (2, 7) and wire_type == kind.LIST:
            element, size = protocol.readListBegin()
            spans = []
            for _ in range(size):
                first = tell()
                protocol.skip(element)
                spans.append((first, tell()))
            protocol.readListEnd()
            result.append((tag, start, tell(), spans))
        else:
            protocol.skip(wire_type)
            if tag in (2, 7):
                result.append((tag, start, tell(), None))
        protocol.readFieldEnd()
    protocol.readStructEnd()
    assert tell() == len(footer)
    return result


def write(path):
    signed = [-(1 << 31), -1, None, 7]
    unsigned = [0, 1 << 31, None, (1 << 32) - 1]
    table = pa.table({"signed": pa.array(signed, pa.int32()),
                      "unsigned": pa.array(unsigned, pa.uint32())})
    pq.write_table(table, path, compression="NONE", data_page_version="2.0",
                   use_dictionary=False, write_page_index=True, write_statistics=True,
                   row_group_size=4, write_batch_size=2, max_rows_per_page=2)
    source = path.read_bytes()
    assert sha256(source).hexdigest() == SHA256
    assert pq.ParquetFile(BytesIO(source)).read(use_threads=False).to_pydict() == table.to_pydict()
    start = len(source) - 8 - struct.unpack("<I", source[-8:-4])[0]
    footer = source[start:-8]
    assert footer.endswith(ORDER_FIELD + b"\0")
    raw, consumed = parse(footer, footer_schema)
    assert consumed == len(footer)
    root, signed_leaf, unsigned_leaf = raw[2]
    assert root[5] == 2
    assert signed_leaf == {1: 1, 4: b"signed"}
    assert unsigned_leaf == {1: 1, 4: b"unsigned", 6: 13, 10: {10: {2: False}}}
    print(f"PyArrow {pa.__version__} fixture {SHA256} footer [{start}, {len(source) - 8})")
    print(f"Thrift original orders {raw[7]}; second leaf converted=13, logical=INTEGER/isSigned=false")
    base_spans = item_extents(footer)
    print(f"original schema and order field/item extents {base_spans}")

    prefix = footer[:-len(ORDER_FIELD) - 1]
    controls = [
        ("second arm 2", "19 2c 1c 00 00 2c 00 00", 2),
        ("second arm 3", "19 2c 1c 00 00 3c 00 00", 2),
        ("second unknown arm", "19 2c 1c 00 00 4c 00 00", 2),
        ("absent", "", None),
        ("short", "19 1c 1c 00 00", 1),
        ("surplus", "19 3c 1c 00 00 1c 00 00 1c 00 00", 3),
        ("wrong list field type", "15 00", None),
        ("wrong element type", "19 21 01 01", 2),
        ("empty second union", "19 2c 1c 00 00 00", 2),
        ("two second arms", "19 2c 1c 00 00 1c 00 1c 00 00", 2),
        ("nonempty second marker", "19 2c 1c 00 00 1c 11 00 00", 2),
        ("first arm 2 with boolean payload", "19 2c 21 00 1c 00 00", 2),
    ]
    for label, field_hex, count in controls:
        modified = prefix + bytes.fromhex(field_hex) + b"\0"
        file = source[:start] + modified + struct.pack("<I", len(modified)) + b"PAR1"
        spans = item_extents(modified)
        assert spans[0] == base_spans[0]
        extent = spans[1][3] if len(spans) == 2 else None
        assert (len(extent) if extent is not None else None) == count
        if label in {"second arm 2", "second arm 3", "second unknown arm", "absent", "short"}:
            observed, end = parse(modified, footer_schema)
            assert end == len(modified) and observed[2] == raw[2]
            expected = {"second arm 2": [{1: {}}, {2: {}}],
                        "second arm 3": [{1: {}}, {3: {}}],
                        "second unknown arm": [{1: {}}, {}],
                        "absent": None, "short": [{1: {}}]}
            assert observed.get(7) == expected[label]
        print(f"{label}: {sha256(file).hexdigest()} order items {extent}")

    duplicate = prefix + ORDER_FIELD + bytes.fromhex("09 0e") + ORDER_FIELD[1:] + b"\0"
    spans = item_extents(duplicate)
    assert [span[0] for span in spans] == [2, 7, 7]
    assert all(len(span[3]) == 2 for span in spans[1:])
    file = source[:start] + duplicate + struct.pack("<I", len(duplicate)) + b"PAR1"
    print(f"duplicate field 7: {sha256(file).hexdigest()} order fields {spans[1:]}")


if __name__ == "__main__":
    write(Path(sys.argv[1]))
