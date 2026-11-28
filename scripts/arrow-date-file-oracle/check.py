"""Regenerate and check the pinned Arrow DATE IPC file observations."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import struct
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
LEAN = ROOT / "Silmaril/Formats/Arrow/DateFile/Fixture.lean"
DAY = 86_400_000
WIDE_DAY = (2**63 - 1) // DAY
EOS = b"\xff\xff\xff\xff\0\0\0\0"
FIELD = "日付"
CASES = {
    "date32": (32, True, [[-(2**31), -1, None], [], [11016, 2**31 - 1]]),
    "date64": (64, True, [[-WIDE_DAY * DAY, -DAY, None], [], [11016 * DAY, WIDE_DAY * DAY]]),
    "schema_only": (32, False, []),
    "late_fraction": (64, True, [[-DAY, None], [], [0, -1]]),
}


def slot(data, table, index):
    vtable = table - struct.unpack_from("<i", data, table)[0]
    size = struct.unpack_from("<H", data, vtable)[0]
    offset = 4 + 2 * index
    if offset + 2 <= size:
        relative = struct.unpack_from("<H", data, vtable + offset)[0]
        if relative:
            return table + relative
    return None


def target(data, position):
    return position + struct.unpack_from("<I", data, position)[0]


def footer_info(wire):
    assert wire[:8] == b"ARROW1\0\0" and wire[-6:] == b"ARROW1"
    footer = len(wire) - 10 - struct.unpack_from("<I", wire, len(wire) - 10)[0]
    assert wire[footer - 8:footer] == EOS
    root = target(wire, footer)
    schema = target(wire, slot(wire, root, 1))
    fields = target(wire, slot(wire, schema, 1))
    assert struct.unpack_from("<I", wire, fields)[0] == 1
    field = target(wire, fields + 4)
    assert wire[slot(wire, field, 2)] == 8  # Date union tag
    date = target(wire, slot(wire, field, 3))
    unit_slot = slot(wire, date, 0)
    vector_slot = slot(wire, root, 3)
    blocks = []
    if vector_slot is not None:
        vector = target(wire, vector_slot)
        count = struct.unpack_from("<I", wire, vector)[0]
        blocks = [list(struct.unpack_from("<qi4xq", wire, vector + 4 + 24 * i))
                  for i in range(count)]
    return footer, unit_slot, blocks


def produce(pa, bits, nullable, batches):
    date_type, storage = (pa.date32(), pa.int32()) if bits == 32 else (pa.date64(), pa.int64())
    schema = pa.schema([pa.field(FIELD, date_type, nullable=nullable)])
    sink = pa.BufferOutputStream()
    with pa.ipc.new_file(sink, schema) as file:
        for slots in batches:
            values = pa.array(slots, type=storage).view(date_type)
            file.write_batch(pa.RecordBatch.from_arrays([values], schema=schema))
    wire = sink.getvalue().to_pybytes()
    file = pa.ipc.open_file(wire)
    assert file.schema == schema and file.num_record_batches == len(batches)
    assert [file.get_batch(i).column(0).view(storage).to_pylist()
            for i in reversed(range(len(batches)))] == list(reversed(batches))
    footer, unit_slot, blocks = footer_info(wire)
    assert len(blocks) == len(batches)
    if bits == 32:
        assert unit_slot is not None and struct.unpack_from("<h", wire, unit_slot)[0] == 0
    else:
        assert unit_slot is None

    stream_bytes = wire[8:footer]
    with pa.ipc.open_stream(stream_bytes) as stream:
        assert stream.schema == schema
        assert [batch.column(0).view(storage).to_pylist() for batch in stream] == batches
    return wire, stream_bytes, footer, unit_slot, blocks


def digest(wire):
    return {"bytes": len(wire), "sha256": hashlib.sha256(wire).hexdigest()}



def fixtures(pa):
    manifest = {}
    wires = {}
    for name, (bits, nullable, batches) in CASES.items():
        wire, stream, footer, unit_slot, blocks = produce(pa, bits, nullable, batches)
        wires[name] = wire
        manifest[name] = {
            **digest(wire), "embedded_stream": digest(stream), "footer_start": footer,
            "footer_date_unit_slot": unit_slot, "blocks": blocks, "word_bits": bits,
            "nullable": nullable, "raw_batches": batches,
        }

    original = wires["date32"]
    unit = manifest["date32"]["footer_date_unit_slot"]
    patched = original[:unit] + b"\x01" + original[unit + 1:]
    assert [(i, byte) for i, byte in enumerate(patched) if byte != original[i]] == [(unit, 1)]
    assert pa.ipc.open_file(patched).schema.field(0).type == pa.date64()
    wires["wrong_footer_unit"] = patched
    manifest["wrong_footer_unit"] = {
        **digest(patched), "source": "date32", "changed_byte": unit,
        "embedded_unit": "DAY", "footer_unit": "MILLISECOND",
    }

    offset, metadata_length, body_length = manifest["date32"]["blocks"][-1]
    message = target(original, offset + 8)
    body_length_slot = slot(original, message, 3)
    assert struct.unpack_from("<Q", original, body_length_slot)[0] == body_length
    manifest["selected_length_controls"] = {
        "metadata_length_offset": offset + 4, "metadata_length_replacement": metadata_length - 16,
        "body_length_offset": body_length_slot, "body_length_replacement": body_length + 8,
        "selected_batch": 2,
    }
    return wires, manifest


def render_lean(wires, manifest):
    lines = [
        "module", "", "public import Silmaril.Prelude.Bytes.Defs", "",
        "-- Generated by scripts/arrow-date-file-oracle/check.py from PyArrow 26.0.1.",
        "@[expose] public section", "",
        "namespace Silmaril.Formats.Arrow.DateFile.Fixture", "",
    ]
    for name, wire in wires.items():
        first, *rest = name.split("_")
        lean_name = first + "".join(part.capitalize() for part in rest)
        lines.extend([f"def {lean_name} : KBytes :=",
                      f"  .leaf {len(wire)} 0x{int.from_bytes(wire, 'little'):x}", ""])
    controls = manifest["selected_length_controls"]
    for name in ("metadata_length_offset", "metadata_length_replacement",
                 "body_length_offset", "body_length_replacement"):
        first, *rest = name.split("_")
        lean_name = first + "".join(part.capitalize() for part in rest)
        lines.append(f"def {lean_name} : Nat := {controls[name]}")
    lines.extend(["", "end Silmaril.Formats.Arrow.DateFile.Fixture", ""])
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pyarrow-path", type=Path, help="Directory containing unpacked PyArrow")
    parser.add_argument("--regenerate", action="store_true", help="Write the pinned manifest and fixture module")
    args = parser.parse_args()
    if args.pyarrow_path is not None:
        sys.path.insert(0, str(args.pyarrow_path.resolve()))
    import pyarrow as pa

    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == "26.0.1"
    wires, cases = fixtures(pa)
    manifest = {
        "cpython": "3.13.5",
        "pyarrow": pa.__version__,
        "pyarrow_wheel_sha256": "f71221bbc7707e3fad920d0478db9350791d4714ec445299ee0d56559fbc156c",
        "cases": cases,
    }
    lean_source = render_lean(wires, cases)
    manifest_path = HERE / "fixtures.json"
    if args.regenerate:
        manifest_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
        LEAN.write_text(lean_source, encoding="utf-8")
    else:
        assert manifest == json.loads(manifest_path.read_text(encoding="utf-8"))
        assert lean_source == LEAN.read_text(encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(LEAN.with_name("Tests.lean"))],
                       cwd=ROOT, check=True)
    print("PASS four PyArrow DATE files and one footer-only DateUnit mutation")


if __name__ == "__main__":
    main()
