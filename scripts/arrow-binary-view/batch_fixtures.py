#!/usr/bin/env python3
"""Reproduce the one-field view RecordBatch fixture module with pinned PyArrow."""

import argparse
import hashlib
from pathlib import Path
import runpy
import struct
import sys


SCRIPT = Path(__file__).resolve()
FIXTURE = SCRIPT.parents[2] / "Silmaril/Formats/Arrow/BinaryView/Batch/Fixture.lean"


def slot_at(buf, table, slot):
    vtable = table - struct.unpack_from("<i", buf, table)[0]
    size = struct.unpack_from("<H", buf, vtable)[0]
    entry = vtable + 4 + 2 * slot
    if entry + 2 > vtable + size:
        return None
    displacement = struct.unpack_from("<H", buf, entry)[0]
    return (entry, table + displacement) if displacement else None


def target(buf, offset):
    return offset + struct.unpack_from("<I", buf, offset)[0]


def vector_at(buf, offset, fmt):
    start = target(buf, offset)
    size = struct.unpack_from("<I", buf, start)[0]
    stride = struct.calcsize(fmt)
    return start, [struct.unpack_from(fmt, buf, start + 4 + i * stride) for i in range(size)]


def producer_batches(pa):
    reference = runpy.run_path(str(SCRIPT.with_name("fixtures.py")))
    if sys.byteorder != "little" or pa.__version__ != reference["PYARROW_VERSION"]:
        raise SystemExit("fixture requires little-endian PyArrow 26.0.1")
    arrays = {
        "mixed": pa.concat_arrays([
            pa.array(values, type=pa.string_view()) for values in reference["VALUES"]
        ]),
        "binary": pa.array([None, b"\xff", b"0123456789abcdef"], type=pa.binary_view()),
        "inline": pa.array(["", None, "α", "abcdefghijkl"], type=pa.string_view()),
        "empty": pa.array([], type=pa.binary_view()),
        "primitive": pa.array([1, None, 2], type=pa.int32()),
    }
    return {name: pa.record_batch([array], names=["value"]) for name, array in arrays.items()}


def ipc_stream(pa, schema, batch=None):
    options = pa.ipc.IpcWriteOptions(metadata_version=pa.ipc.MetadataVersion.V5,
                                      use_legacy_format=False, compression=None)
    sink = pa.BufferOutputStream()
    with pa.ipc.new_stream(sink, schema, options=options) as writer:
        if batch is not None:
            writer.write_batch(batch)
    return sink.getvalue()


def produce():
    import pyarrow as pa

    batches = producer_batches(pa)
    expected_counts = {"mixed": 2, "binary": 1, "inline": 1, "empty": 0}
    output = [
        "module\n\npublic import Silmaril.Prelude.Bytes.Defs\n\n",
        "/-! Reproduced by scripts/arrow-binary-view/batch_fixtures.py. -/\n\n",
        "@[expose] public section\n\n",
        "namespace Silmaril.Formats.Arrow.BinaryView.Batch.Fixture\n\n",
    ]
    for name, record in batches.items():
        array = record.column(0)
        stream = ipc_stream(pa, record.schema, record)
        _, message = pa.ipc.MessageReader.open_stream(stream)
        meta = message.metadata.to_pybytes()
        body = message.body.to_pybytes()
        if pa.ipc.open_stream(stream).read_next_batch().column(0).to_pylist() != array.to_pylist():
            raise SystemExit(f"unexpected PyArrow readback for {name}")
        for suffix, value in (("Metadata", meta), ("Body", body)):
            if name == "primitive" and suffix == "Body":
                continue
            output.append(f"def {name}{suffix} : KBytes :=\n")
            output.append(f"  .leaf {len(value)} 0x{int.from_bytes(value, 'little'):x}\n\n")
        if name != "primitive":
            root = struct.unpack_from("<I", meta)[0]
            _, payload_ref = slot_at(meta, root, 2)
            payload = target(meta, payload_ref)
            _, node_ref = slot_at(meta, payload, 1)
            _, buffer_ref = slot_at(meta, payload, 2)
            count_slot, count_ref = slot_at(meta, payload, 4)
            node_vector, nodes = vector_at(meta, node_ref, "<qq")
            buffer_vector, descriptors = vector_at(meta, buffer_ref, "<qq")
            count_vector, counts = vector_at(meta, count_ref, "<q")
            expected_count = expected_counts[name]
            if (nodes != [(len(array), array.null_count)] or counts != [(expected_count,)] or
                    len(descriptors) != 2 + expected_count):
                raise SystemExit(f"unexpected view layout for {name}")
            if name == "mixed":
                offsets = {
                    "mixedCountSlot": count_slot, "mixedCountVector": count_vector,
                    "mixedCountWord": count_vector + 4, "mixedFirstNode": node_vector + 4,
                    "mixedViewsDescriptor": buffer_vector + 4 + 16,
                }
                for label, offset in offsets.items():
                    output.append(f"def {label} : Nat := {offset}\n\n")
            print(f"{name}: counts={[expected_count]}, descriptors={descriptors}")
        print(f"{name}: IPC stream SHA-256 {hashlib.sha256(stream).hexdigest()}")
    output.append("end Silmaril.Formats.Arrow.BinaryView.Batch.Fixture\n")
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
