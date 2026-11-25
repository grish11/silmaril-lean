"""Compare wide rowid varints in stock- and Lean-created SQLite images."""
import tempfile
from pathlib import Path

from check import SCHEMA, check_image, create, oracle, row_arguments, successful

BOUNDARY = 2**56
KEYS = [-(2**63), -(2**63) + 128, -1, BOUNDARY - 1, BOUNDARY, BOUNDARY + 255, 2**63 - 1]
ENTRIES = list(zip(KEYS, range(len(KEYS))))


def rowid_bytes(image):
    base = 512
    count = int.from_bytes(image[base + 3:base + 5], "big")
    assert image[base] == 13 and count == len(KEYS)
    result = []
    for slot, key in enumerate(KEYS):
        pointer = base + 8 + 2 * slot
        cell = base + int.from_bytes(image[pointer:pointer + 2], "big")
        # Each payload length fits in one byte, so the rowid follows it.
        assert 3 <= image[cell] < 128
        start = cell + 1
        width = 8 if key == BOUNDARY - 1 else 9
        stop = start + width
        encoded = image[start:stop]
        assert len(encoded) == width and all(byte >= 128 for byte in encoded[:-1])
        if width == 8:
            assert encoded == b"\xff" * 7 + b"\x7f"
        else:
            assert encoded[-1] == key % 256
        if key == -1:
            # The signed rowid -1 is the maximum unsigned bit pattern on disk.
            assert encoded == b"\xff" * 9
        # The record starts exactly where the rowid ends.
        assert image[stop] == 3
        result.append(encoded)
    return result


def main():
    with tempfile.TemporaryDirectory() as temp:
        directory = Path(temp)
        native = oracle(directory)
        native_path = directory / "varint-native.sqlite"
        lean_path = directory / "varint-lean.sqlite"
        rows = ",".join(f"({key},{amount})" for key, amount in ENTRIES)
        successful(native(native_path, f"PRAGMA page_size=512; {SCHEMA}; "
                                       f"INSERT INTO sample VALUES {rows}; VACUUM;"))
        successful(create(lean_path, *row_arguments(ENTRIES)))
        native_bytes = rowid_bytes(check_image(native, native_path, ENTRIES))
        lean_bytes = rowid_bytes(check_image(native, lean_path, ENTRIES))
        assert lean_bytes == native_bytes, (lean_bytes, native_bytes)
    print("Both readers reopened both images, stock integrity_check passed, and rowid bytes agreed.")


if __name__ == "__main__":
    main()
