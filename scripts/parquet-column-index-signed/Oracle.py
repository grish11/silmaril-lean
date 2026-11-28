"""Reproduce the V2 fixture and validate shape-preserving V1 mutations."""

from hashlib import sha256
from io import BytesIO
from itertools import pairwise
from operator import ge, le
from pathlib import Path
import runpy
import struct
import sys

oracle = runpy.run_path(
    str(Path(__file__).resolve().parents[1] / "parquet-column-index" / "Oracle.py"))
pa, pq = oracle["pa"], oracle["pq"]
parse, patch = oracle["parse"], oracle["patch"]
ROWS = oracle["ROWS"]
ORDERS = oracle["ORDERS"]
V2_SHA256 = "bc056132b17307c091698d43841db26dbffc1e8a41eba5c4a7ac1aafff74760a"
PAGE_V2 = {1: oracle["I32"], 3: oracle["I32"],
           8: oracle["record"]({field: oracle["I32"] for field in range(1, 7)})}


def footer(source):
    start = len(source) - 8 - struct.unpack("<I", source[-8:-4])[0]
    metadata, consumed = parse(source[start:-8], oracle["FOOTER"])
    assert consumed == len(source) - 8 - start
    return start, metadata


def signed_claims(source, group):
    start, metadata = footer(source)
    [column] = metadata[4][group][1]
    wire = oracle["checked_span"](source, start, column[6], column[7], oracle["COLUMN_INDEX"])
    positions = oracle["checked_span"](source, start, column[4], column[5], oracle["OFFSET_INDEX"])[1]
    assert len(positions) == len(wire[1]) == len(wire[2]) == len(wire[3]) == 3
    assert [entry[3] for entry in positions] == [0, 4, 8]
    assert all((len(lo), len(hi)) == ((0, 0) if is_null else (4, 4))
               for is_null, lo, hi in zip(wire[1], wire[2], wire[3], strict=True))
    if 5 in wire:
        assert len(wire[5]) == 3
        assert all(0 <= n <= 4 and (n == 4) == is_null
                   for n, is_null in zip(wire[5], wire[1], strict=True))
    bounds = [None if is_null else (struct.unpack("<i", lo)[0], struct.unpack("<i", hi)[0])
              for is_null, lo, hi in zip(wire[1], wire[2], wire[3], strict=True)]
    return wire, positions, bounds


def compare(source, group):
    wire, _, bounds = signed_claims(source, group)
    slots = pq.ParquetFile(BytesIO(source)).read_row_group(group).column(0).to_pylist()
    assert slots == ROWS[group]
    pages = [slots[i:i + 4] for i in range(0, len(slots), 4)]
    present = [[value for value in page if value is not None] for page in pages]
    flags = [not values for values in present] == wire[1]
    counts = 5 not in wire or [page.count(None) for page in pages] == wire[5]
    containment = all(bound is not None and bound[0] <= value <= bound[1]
                      for bound, values in zip(bounds, present, strict=True) for value in values)
    ordered_bounds = [bound for bound in bounds if bound is not None]
    compare_endpoints = {1: le, 2: ge}.get(wire[4])
    order = tuple(compare_endpoints is None or all(compare_endpoints(a[i], b[i])
                  for a, b in pairwise(ordered_bounds)) for i in (0, 1))
    return flags, counts, containment, *order


def check_v1(source):
    assert sha256(source).hexdigest() == oracle["FIXTURE_SHA256"]
    assert all(compare(source, group) == (True,) * 5 for group in range(3))
    # Re-encode only the group-zero ColumnIndex. The eight added bound bytes replace
    # an unused repetition/definition histogram field. All advertised spans stay put.
    false_flag = (patch(source, (294, 1, 2))[:303] + b"\x04\0\0\0\0"
                  + source[304:316] + b"\x04\x03\0\0\0"
                  + patch(source, (327, 8, 6))[317:329] + b"\0" + source[338:])
    assert len(false_flag) == len(source)
    no_counts = patch(source, (324, 0x19, 0), (641, 94, 68))
    controls = [
        ("loose upper", patch(source, (312, 3, 4)), 0, (True,) * 5),
        ("excluded value", patch(source, (312, 3, 2)), 0, (True, True, False, True, True)),
        ("wrong null count", patch(source, (326, 2, 0)), 0, (True, False, True, True, True)),
        ("descending upper inversion", patch(source, (365, 8, 13)), 1,
         (True, True, True, True, False)),
        ("ascending lower inversion", patch(source, (425, 0, 2), (420, 5, 12)), 2,
         (True, True, True, False, True)),
        ("false all-null flag", false_flag, 0, (False, False, True, True, True)),
        ("missing null counts", no_counts, 0, (True,) * 5),
    ]
    for label, modified, group, expected in controls:
        result = compare(modified, group)
        assert result == expected
        print(f"{label}: {sha256(modified).hexdigest()} {result}")
    assert 5 not in signed_claims(no_counts, 0)[0]


def check_metadata_and_payload(source):
    # Add the legacy UINT_32 annotation to the selected leaf, keeping the
    # original chunk and index spans. Grow the final footer size by two bytes.
    annotated = source[:547] + b"\x25\x1a" + source[547:-8] + struct.pack("<I", 590) + b"PAR1"
    _, metadata = footer(annotated)
    assert metadata[2][1] == {1: 1, 6: 13} and metadata[7] == [{1: {}}]
    assert signed_claims(annotated, 0) == signed_claims(source, 0)
    unsigned = pq.ParquetFile(BytesIO(annotated)).read_row_group(0).column(0)
    assert unsigned.type == pa.uint32()
    assert unsigned.to_pylist() == [None if value is None else value % (1 << 32) for value in ROWS[0]]
    print(f"UINT_32 annotation: {sha256(annotated).hexdigest()}")

    missing = source[:1100] + b"\0" + struct.pack("<I", 583) + b"PAR1"
    _, metadata = footer(missing)
    assert 7 not in metadata and compare(missing, 0) == (True,) * 5
    print(f"absent column order: {sha256(missing).hexdigest()}")

    malformed = patch(source, (79, 2, 17))
    assert signed_claims(malformed, 0) == signed_claims(source, 0)
    try:
        pq.ParquetFile(BytesIO(malformed)).read_row_group(0)
    except (pa.ArrowInvalid, OSError):
        print(f"late malformed definition extent: {sha256(malformed).hexdigest()}")
    else:
        raise AssertionError("PyArrow accepted a truncated late definition section")


def write_v2(path):
    values = pa.array([value for group in ROWS for value in group], type=pa.int32())
    pq.write_table(pa.table({"number": values}), path, data_page_version="2.0",
                   compression="NONE", use_dictionary=False, write_page_index=True,
                   write_statistics=True, row_group_size=12, write_batch_size=4,
                   max_rows_per_page=4)
    source = path.read_bytes()
    assert sha256(source).hexdigest() == V2_SHA256
    _, metadata = footer(source)
    assert metadata[2] == [{}, {1: 1}] and metadata[7] == [{1: {}}]
    print(f"{path.name}: {V2_SHA256}")
    for group, (label, order) in enumerate(ORDERS):
        wire, positions, bounds = signed_claims(source, group)
        assert wire[4] == order and compare(source, group) == (True,) * 5
        for page, count in zip(positions, wire[5], strict=True):
            start, size = page[1], page[2]
            header, consumed = parse(source[start:start + size], PAGE_V2)
            fields = header[8]
            assert header[1] == 3 and consumed + header[3] == size
            assert (fields[1], fields[2], fields[3], fields[4], fields[6]) == (4, count, 4, 0, 0)
        print(f"V2 group {group} {label}: bounds {bounds}, null counts {wire[5]}")


if __name__ == "__main__":
    print("Control columns: all-null agreement, null counts, containment, lower order, upper order")
    source = Path("data/parquet-column-index/column-index.parquet").read_bytes()
    check_v1(source)
    check_metadata_and_payload(source)
    write_v2(Path(sys.argv[1]))
