#!/usr/bin/env python3
"""Pin Arrow JS files, check their indexed PyArrow observation, and embed their exact bytes."""

import argparse
import hashlib
from pathlib import Path
import struct
import sys

import pyarrow as pa


MODULE = Path(__file__).resolve().parents[2] / "Silmaril/Formats/Arrow/FileReader/FooterOnly/Fixture.lean"
EOS = b"\xff\xff\xff\xff\0\0\0\0"
FIELDS = pa.schema([("signed", pa.int32()), ("text", pa.utf8())])
CASES = {
    "multi": ("de4a0d6379f8a9ba76b94dfa1f256556151cdcc06ab70c506c4ed2370ae808ab", 704, 248,
              [(8, 208, 176), (392, 208, 96)], [
                  {"signed": [-7, None, 42, -2147483648], "text": ["é", None, "", "雪"]},
                  {"signed": [0, 2147483647], "text": [None, "tail"]},
              ]),
    "schemaOnly": ("f1f051b3f2b6f9571c1e7f5dc23ca634e5f9d20a7119092f4444cbba65fc2cd8", 16, 200, [], []),
}


def block_vector(data, footer):
    root = footer + struct.unpack_from("<I", data, footer)[0]
    vtable = root - struct.unpack_from("<i", data, root)[0]
    record_batches = root + struct.unpack_from("<H", data, vtable + 10)[0]
    vector = record_batches + struct.unpack_from("<I", data, record_batches)[0]
    count = struct.unpack_from("<I", data, vector)[0]
    start = vector + 4
    return start, [struct.unpack_from("<qi4xq", data, start + 24 * i) for i in range(count)]


def check(name, data):
    digest, footer, length, blocks, expected = CASES[name]
    assert hashlib.sha256(data).hexdigest() == digest
    assert data[:8] == b"ARROW1\0\0" and data[-6:] == b"ARROW1"
    assert struct.unpack_from("<i", data, len(data) - 10) == (length,)
    assert footer + length + 10 == len(data) and data[footer-8:footer] == EOS
    start, declared = block_vector(data, footer)
    assert declared == blocks
    cursor = 8
    for offset, metadata, body in blocks:
        assert offset == cursor and struct.unpack_from("<II", data, offset) == (0xFFFFFFFF, metadata - 8)
        cursor += metadata + body
    assert cursor + 8 == footer
    if blocks:
        assert pa.ipc.read_message(data[8:footer]).type == "record batch"

    with pa.ipc.open_file(data) as reader:
        assert reader.schema.equals(FIELDS, check_metadata=True)
        assert reader.num_record_batches == len(expected)
        selected = {}
        for i in reversed(range(reader.num_record_batches)):
            batch = reader.get_batch(i)
            batch.validate(full=True)
            selected[i] = batch.to_pydict()
        assert [selected[i] for i in range(reader.num_record_batches)] == expected
    print(f"{name}: SHA-256 {digest}, footer ({footer}, {length}), block vector {start}, "
          f"blocks {blocks}, rows {[len(batch['signed']) for batch in expected]}")
    return start


def main():
    if sys.byteorder != "little" or pa.__version__ != pa.cpp_build_info.version or pa.__version__ != "26.0.1":
        raise SystemExit("requires little-endian PyArrow 26.0.1")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", type=Path)
    parser.add_argument("--write", action="store_true", help="write the Lean fixture module")
    args = parser.parse_args()
    lines = [
        "module", "", "public import Silmaril.Prelude.Bytes.Defs", "",
        "/-! Exact Arrow JS 21.2.0 file bytes. Reproduce with scripts/arrow-footer-only-file. -/", "",
        "@[expose] public section", "",
        "namespace Silmaril.Formats.Arrow.FileReader.FooterOnly.Fixture", "",
    ]
    for name in CASES:
        data = (args.files / f"{name}.arrow").read_bytes()
        start = check(name, data)
        lines += [f"def {name} : KBytes :=",
                  f"  .leaf {len(data)} 0x{int.from_bytes(data, 'little'):x}", ""]
        if name == "multi":
            lines += [f"def multiBlocks : Nat := {start}", ""]
    lines += ["end Silmaril.Formats.Arrow.FileReader.FooterOnly.Fixture", ""]
    embedded = "\n".join(lines)
    if args.write:
        MODULE.write_text(embedded, encoding="utf-8")
    elif MODULE.read_text(encoding="utf-8") != embedded:
        raise SystemExit("pinned Arrow JS files differ from the Lean fixture")


if __name__ == "__main__":
    main()
