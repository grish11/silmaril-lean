"""Generate timestamp schemas with PyArrow and verify the complete Lean IPC output."""

import argparse
import csv
from dataclasses import dataclass, replace
import hashlib
from io import StringIO
import os
from pathlib import Path
import platform
from runpy import run_path
import subprocess

import pyarrow as pa


ROOT = Path(__file__).resolve().parents[2]
WIRE = run_path(str(ROOT / "tests/formats/arrow-timestamp-stream/check-fixtures.py"))
EOS = bytes.fromhex("ffffffff00000000")
EXPECTED_DIGEST = "679d39636cddc700e5d91c27c41c5c853e74a4745017488d64fa1f1b3e79b543"


@dataclass(frozen=True)
class Descriptor:
    unit: str
    zone: str | None
    nullable: bool = True
    field: str = "event time"

    def schema(self):
        return pa.schema([pa.field(self.field, pa.timestamp(self.unit, self.zone or None), self.nullable)])


def frame_for(descriptor, version=pa.ipc.MetadataVersion.V5):
    # PyArrow uses an absent field for a local timestamp. Retain an explicit
    # empty annotation using the pinned reader oracle's FlatBuffers fixture.
    physical = replace(descriptor, zone="UTC") if descriptor.zone == "" else descriptor
    output = pa.BufferOutputStream()
    with pa.ipc.new_stream(output, physical.schema(), options=pa.ipc.IpcWriteOptions(metadata_version=version)):
        pass
    wire = output.getvalue().to_pybytes()
    if descriptor.zone == "":
        wire = WIRE["explicit_empty_timezone"](wire)
    assert wire.endswith(EOS)
    return wire[:-len(EOS)]


def csv_for(descriptor, ticks):
    stream = StringIO(newline="")
    csv.writer(stream, quoting=csv.QUOTE_ALL, lineterminator="\r\n").writerows(
        [[descriptor.field]] + [["N" if tick is None else f"T{tick}"] for tick in ticks]
    )
    return stream.getvalue().encode("utf-8")


def invoke(mode, source, schema, output, descriptor):
    subprocess.run([
        os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
        "--run", str(Path(__file__).with_name("Emit.lean")), mode, str(source), str(schema), str(output),
        descriptor.field, descriptor.unit, str(descriptor.zone is not None).lower(), descriptor.zone or "",
        str(descriptor.nullable).lower(),
    ], cwd=ROOT, check=True)


def fixtures():
    minimum, maximum = -(2**63), 2**63 - 1
    for label, descriptor, ticks in (
        ("local-seconds", Descriptor("s", None), [-1, None, 0]),
        ("utc-millis", Descriptor("ms", "UTC"), [0, None, -2001]),
        ("required-micros", Descriptor("us", "+05:45", False), [-2001, 0, 1]),
        ("zoned-nanos", Descriptor("ns", "Asia/Kathmandu"), [minimum, None, -1, 0, maximum]),
        ("present-empty-zone", Descriptor("ns", ""), [-1, 0, None]),
        ("zero-rows", Descriptor("s", None), []),
    ):
        yield label, "ok", descriptor, frame_for(descriptor), csv_for(descriptor, ticks), ticks

    zoned = Descriptor("ns", "Asia/Kathmandu")
    frame = frame_for(zoned)
    wire = csv_for(zoned, [minimum, None, 0, maximum])
    required = Descriptor("ns", zoned.zone, False)
    two_columns = pa.schema([zoned.schema().field(0), pa.field("other", pa.timestamp("ns"))])
    output = pa.BufferOutputStream()
    with pa.ipc.new_stream(output, two_columns):
        pass
    tests = [
        ("wrong-name", "schema-mismatch", replace(zoned, field="other"), frame, wire),
        ("wrong-unit", "schema-mismatch", replace(zoned, unit="us"), frame, wire),
        ("wrong-zone", "schema-mismatch", replace(zoned, zone="UTC"), frame, wire),
        ("local-vs-zoned", "schema-mismatch", replace(zoned, zone=None), frame, wire),
        ("absent-vs-empty-zone", "schema-mismatch", Descriptor("ns", None), frame_for(Descriptor("ns", "")), wire),
        ("wrong-nullability", "schema-mismatch", required, frame, wire),
        ("extra-frame", "extra-frame", zoned, frame + EOS, wire),
        ("truncated-frame", "truncated-frame", zoned, frame[:-1], wire),
        ("v4", "v4", zoned, frame_for(zoned, pa.ipc.MetadataVersion.V4), wire),
        ("two-fields", "shape", zoned, output.getvalue().to_pybytes()[:-len(EOS)], wire),
        ("bad-csv", "bad-csv", zoned, frame, b'"event time"\r\n"T\xc0"\r\n'),
        ("bad-header", "bad-header", zoned, frame, csv_for(replace(zoned, field="other"), [0])),
        ("bad-tick", "bad-tick", zoned, frame, b'"event time"\r\n"T01"\r\n'),
        ("required-null", "required-null", required, frame_for(required), wire),
        ("occupied", "occupied", zoned, frame[:-1], wire),
    ]
    tests += [(mode, mode, zoned, frame, wire) for mode in (
        "csv-bytes", "csv-rows", "ipc-rows", "ipc-body", "ipc-batches"
    )]
    for label, mode, descriptor, schema, csv_bytes in tests:
        yield label, mode, descriptor, schema, csv_bytes, None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    directory = parser.parse_args().out.resolve()
    directory.mkdir(parents=True, exist_ok=True)
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1"
    cases = list(fixtures())
    digest = hashlib.sha256()
    for _, _, _, frame, wire, _ in cases:
        for value in (frame, wire):
            digest.update(len(value).to_bytes(8, "little"))
            digest.update(value)
    assert digest.hexdigest() == EXPECTED_DIGEST, f"fixture SHA-256 {digest.hexdigest()}"
    for label, mode, descriptor, frame, wire, ticks in cases:
        source = directory / f"{label}.csv"
        schema = directory / f"{label}.schema"
        output = directory / f"{label}.arrows"
        source.write_bytes(wire)
        schema.write_bytes(frame)
        output.unlink(missing_ok=True)
        invoke(mode, source, schema, output, descriptor)
        if mode == "ok":
            emitted = output.read_bytes()
            assert emitted.startswith(frame) and emitted.endswith(EOS)
            with pa.ipc.open_stream(emitted) as stream:
                assert stream.schema == descriptor.schema(), label
                batches = list(stream)
                assert [batch.column(0).cast(pa.int64()).to_pylist() for batch in batches] == [ticks], label
            sha256 = hashlib.sha256(emitted).hexdigest()
            print(f"{label}: {len(ticks)} rows, {descriptor.unit}, zone {descriptor.zone!r}, {sha256}")
        else:
            assert not output.exists(), label
    print(f"PyArrow {pa.__version__}: six complete IPC streams and {len(cases) - 6} typed failures")
    print(f"Length-framed Schema and CSV fixture SHA-256 {digest.hexdigest()}")


if __name__ == "__main__":
    main()
