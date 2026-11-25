"""Check the small-rowid cell writer against both compiled SQLite readers."""
import tempfile
from pathlib import Path

from check import (
    SCHEMA, SELECT_ROWS, SHELL, check_image, create, oracle, rejected,
    row_arguments, run, successful,
)

ENTRIES = [(0, -(2**63)), (1, 2**63 - 1), (126, -129), (127, 0), (128, 1)]
PAGE_SIZE = 512


def check_cells(image, lean_created):
    page = image[PAGE_SIZE:]
    count = int.from_bytes(page[3:5], "big")
    assert page[0] == 13 and count == len(ENTRIES)
    pointers = range(8, 8 + 2 * count, 2)
    starts = [int.from_bytes(page[pointer:pointer + 2], "big") for pointer in pointers]
    physical = sorted(starts)
    stops = dict(zip(physical, physical[1:] + [PAGE_SIZE]))
    assert len(stops) == count
    for start, (rowid, amount) in zip(starts, ENTRIES):
        assert 8 + 2 * count <= start < PAGE_SIZE
        payload_size = page[start]
        assert 3 <= payload_size < 127
        rowid_bytes = bytes([rowid]) if rowid < 128 else b"\x81\x00"
        payload_at = start + 1 + len(rowid_bytes)
        assert page[start + 1:payload_at] == rowid_bytes
        if lean_created:
            expected = b"\x03\x00\x06" + amount.to_bytes(8, "big", signed=True)
            assert payload_size == len(expected) == 11
            assert stops[start] - start == (13 if rowid < 128 else 14)
            assert page[payload_at:stops[start]] == expected
    return PAGE_SIZE + min(starts)


def check_wrong_extent(native, path, image, start):
    damaged = path.with_name(f"{path.stem}-bad-payload-size.sqlite")
    changed = image[:start] + bytes([image[start] + 1]) + image[start + 1:]
    damaged.write_bytes(changed)
    rejected(run(SHELL, "--immutable", damaged, SELECT_ROWS), "malformed")
    result = native("-readonly", damaged, "PRAGMA integrity_check;")
    assert result.stdout.strip() != "ok", result
    assert result.stdout.strip() or result.stderr.strip(), result


def main():
    with tempfile.TemporaryDirectory() as temp:
        directory = Path(temp)
        native = oracle(directory)
        stock_path = directory / "cell-stock.sqlite"
        lean_path = directory / "cell-lean.sqlite"
        values = ",".join(f"({key},{amount})" for key, amount in ENTRIES)
        successful(native(stock_path, f"PRAGMA page_size=512; {SCHEMA}; "
                                      f"INSERT INTO sample VALUES {values}; VACUUM;"))
        successful(create(lean_path, *row_arguments(ENTRIES)))
        for path in (stock_path, lean_path):
            image = check_image(native, path, ENTRIES)
            start = check_cells(image, path == lean_path)
            check_wrong_extent(native, path, image, start)
    print("Both readers reopened both images. Cell bytes and stock integrity matched.")
    print("Lean rejected the wrong extents, and stock integrity_check flagged them.")


if __name__ == "__main__":
    main()
