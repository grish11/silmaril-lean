"""Check two-byte page fields in stock- and Lean-created SQLite files."""
import tempfile
from pathlib import Path

from check import (
    SCHEMA, SELECT_ROWS, SHELL, check_image, create, oracle, rejected,
    row_arguments, run, successful,
)

PAGE_SIZE = 512
CASES = {
    "empty": [],
    "partial": [(key, -(key + 1)) for key in range(10)],
    "capacity": [(key, -key) for key in [*range(8), *range(128, 152)]],
}


def read_varint(page, offset):
    value = 0
    for index in range(8):
        byte = page[offset + index]
        value = value * 128 + byte % 128
        if byte < 128:
            return value, offset + index + 1
    return value * 256 + page[offset + 8], offset + 9


def check_leaf(page, base, expected_count):
    assert page[base] == 13 and page[base + 7] == 0
    assert page[base + 1:base + 3] == b"\x00\x00"
    count = int.from_bytes(page[base + 3:base + 5], "big")
    content = int.from_bytes(page[base + 5:base + 7], "big")
    pointers_end = base + 8 + 2 * count
    assert count == expected_count and pointers_end <= content <= PAGE_SIZE
    pointers = [int.from_bytes(page[i:i + 2], "big") for i in range(base + 8, pointers_end, 2)]
    assert len(set(pointers)) == count
    assert all(content <= pointer < PAGE_SIZE for pointer in pointers)
    cursor = content
    for pointer in sorted(pointers):
        assert pointer == cursor
        payload_size, key = read_varint(page, pointer)
        _, payload = read_varint(page, key)
        cursor = max(pointer + 4, payload + payload_size)
    assert cursor == PAGE_SIZE
    return content - pointers_end


def check_page_fields(image, expected_count):
    assert image[16:18] == b"\x02\x00"
    check_leaf(image[:PAGE_SIZE], 100, 1)
    return check_leaf(image[PAGE_SIZE:], 0, expected_count)


def check_rejected_images(native, path, image, count):
    cases = [("truncated-page-size", image[:17], "1024-byte")]
    for label, base, has_cells in (("catalogue", 100, True), ("table", PAGE_SIZE, bool(count))):
        fields = [("content", base + 5, b"\x02\x01")]
        if has_cells:
            fields.append(("pointer", base + 8, b"\x02\x00"))
        for field, offset, invalid in fields:
            damaged = image[:offset] + invalid + image[offset + 2:]
            cases.append((f"{label}-out-of-range-{field}", damaged, "malformed"))
    for name, damaged, reason in cases:
        corrupted = path.with_name(f"{path.stem}-{name}.sqlite")
        corrupted.write_bytes(damaged)
        rejected(run(SHELL, "--immutable", corrupted, SELECT_ROWS), reason)
        result = native("-readonly", corrupted, "PRAGMA integrity_check;")
        assert result.stdout.strip() != "ok", result
        assert result.stdout.strip() or result.stderr.strip(), result


def main():
    with tempfile.TemporaryDirectory() as temp:
        directory = Path(temp)
        native = oracle(directory)
        for name, entries in CASES.items():
            native_path = directory / f"{name}-native.sqlite"
            lean_path = directory / f"{name}-lean.sqlite"
            rows = ",".join(f"({key},{amount})" for key, amount in entries)
            statements = f"PRAGMA page_size={PAGE_SIZE}; {SCHEMA}; "
            if rows:
                statements += f"INSERT INTO sample VALUES {rows}; "
            successful(native(native_path, statements + "VACUUM;"))
            successful(create(lean_path, *row_arguments(entries)))
            for path in (native_path, lean_path):
                image = check_image(native, path, entries)
                unused = check_page_fields(image, len(entries))
                if path == lean_path and name == "capacity":
                    assert unused == 0
                check_rejected_images(native, path, image, len(entries))
    print("Both readers reopened valid images. Stock integrity and both packed-leaf headers passed.")
    print("Lean rejected the damaged images, and stock integrity_check flagged them.")


if __name__ == "__main__":
    main()
