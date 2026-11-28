#!/usr/bin/env python3
"""Reproduce the pinned PyArrow mixed-flat Schema, RecordBatch and body slices."""

import argparse
import hashlib
from pathlib import Path
import runpy
import struct
import sys


ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "Silmaril/Formats/Arrow/MixedFlat/Fixture.lean"


def produce():
    import pyarrow as pa

    if sys.byteorder != "little" or pa.__version__ != "26.0.1":
        raise SystemExit("fixture requires little-endian PyArrow 26.0.1")
    wire = runpy.run_path(str(ROOT / "scripts/arrow-binary-view/batch_fixtures.py"))
    slot_at, target, vector_at = (wire[name] for name in ("slot_at", "target", "vector_at"))
    ints = pa.array([1, None, -7, 0], type=pa.int32())
    binary = pa.concat_arrays([
        pa.array([b"x" * 13, None], type=pa.binary_view()),
        pa.array([b"", b"y" * 17], type=pa.binary_view()),
    ])
    utf8 = pa.array(["α", "", None, "last"], type=pa.string())
    view = pa.array([None, "", "short", "雪" * 6], type=pa.string_view())
    columns = (ints, binary, utf8, view)
    names = ("i", "b", "u", "v")
    output = [
        "module\n\npublic import Silmaril.Prelude.Bytes.Defs\n\n",
        "/-! Reproduced by scripts/arrow-mixed-flat/fixtures.py. -/\n\n",
        "@[expose] public section\n\n",
        "namespace Silmaril.Formats.Arrow.MixedFlat.Fixture\n\n",
    ]

    def fixture(label, field_names, arrays, expected_counts, widths):
        batch = pa.record_batch(list(arrays), names=list(field_names))
        stream = wire["ipc_stream"](pa, batch.schema, batch)
        back = pa.ipc.open_stream(stream).read_next_batch()
        assert back.schema.equals(batch.schema) and back.to_pylist() == batch.to_pylist()
        schema, record = pa.ipc.MessageReader.open_stream(stream)
        metadata = record.metadata.to_pybytes()
        body = record.body.to_pybytes()
        root = struct.unpack_from("<I", metadata)[0]
        payload = target(metadata, slot_at(metadata, root, 2)[1])
        count_slot, count_ref = slot_at(metadata, payload, 4)
        count_vector, counts = vector_at(metadata, count_ref, "<q")
        node_vector, nodes = vector_at(metadata, slot_at(metadata, payload, 1)[1], "<qq")
        descriptor_vector, descriptors = vector_at(metadata, slot_at(metadata, payload, 2)[1], "<qq")
        assert [word for (word,) in counts] == expected_counts
        assert nodes == [(len(array), array.null_count) for array in arrays]
        assert len(descriptors) == sum(widths)
        previous_end = 0
        for offset, length in descriptors:
            assert previous_end <= offset and offset % 8 == 0 and 0 <= length <= len(body) - offset
            previous_end = offset + length
        if label == "mixed":
            views_offset, _ = descriptors[3]
            length, _, index, _ = struct.unpack_from("<i4sii", body, views_offset + 3 * 16)
            assert (length, index) == (17, 1)
            for name, offset in (
                ("mixedCountSlot", count_slot),
                ("mixedCountVector", count_vector),
                ("mixedCountWord", count_vector + 4),
                ("mixedThirdNode", node_vector + 4 + 2 * 16),
                ("mixedBinaryValidity", descriptor_vector + 4 + 2 * 16),
                ("mixedDescriptorVector", descriptor_vector),
            ):
                output.append(f"def {name} : Nat := {offset}\n")
            output.append("\n")
        print(f"{label}: counts={expected_counts}, descriptor widths={widths}, "
              f"stream SHA-256 {hashlib.sha256(stream).hexdigest()}")
        for suffix, value in (("Schema", schema.metadata.to_pybytes()), ("Record", metadata), ("Body", body)):
            output.append(f"def {label}{suffix} : KBytes :=\n"
                          f"  .leaf {len(value)} 0x{int.from_bytes(value, 'little'):x}\n\n")

    fixture("mixed", names, columns, [2, 1], [2, 4, 3, 3])
    order = (3, 2, 1, 0)
    fixture("reordered", [names[i] for i in order], [columns[i] for i in order], [1, 2], [3, 3, 4, 2])
    fixture("empty", names, [pa.array([], type=column.type) for column in columns], [0, 0], [2, 2, 3, 2])
    output.append("end Silmaril.Formats.Arrow.MixedFlat.Fixture\n")
    return "".join(output)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", type=Path, help="write the reproduced Lean fixture to this path")
    args = parser.parse_args()
    reproduced = produce()
    if args.write:
        args.write.write_text(reproduced, encoding="utf-8")
    elif FIXTURE.read_text(encoding="utf-8") != reproduced:
        raise SystemExit("reproduced fixture differs from checked Lean bytes")


if __name__ == "__main__":
    main()
