"""Compare original and returned IPC through genuine Lean Parquet files."""

import argparse
from hashlib import sha256
from importlib.metadata import version
import os
from pathlib import Path
from runpy import run_path
import subprocess
import sys

import pyarrow as pa


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
FORWARD = ROOT / "scripts/arrow-mixed-ipc-to-parquet-oracle/check.py"
ARROW = ROOT / "scripts/arrow-mixed-named-oracle/check.py"
PARQUET = ROOT / "scripts/parquet-mixed-v1-writer-oracle/check.py"
THRIFT = ROOT / "tests/formats/parquet-timestamp-leaf/check-fixtures.py"
VIEW_PINS = {
    "view-first-empty-returned.arrows": "69e2f0d9437ba88f091882b07ead54fdecd1f16253d18c5ebcaaa3ed0d96a6d4",
    "view-first-empty.arrows": "a77f0cd32a450a0d87d7099872d0f3c5c8f33f6f1639e8cfb5a68bb22f72b34f",
    "view-first-empty.parquet": "d6e41f0ce9992a6d80ce72085667d1bc85e38c7045c12fd3f766e68766699597",
    "view-first-returned.arrows": "af9bbccfefe98a882dad1ae8bd7615e854980eb41b3e7f448bb8f55d619f48c0",
    "view-first-schema-only.arrows": "d177a80b8a239cab0ee459f90c9eda9bb84a258bf6b808fe7349e997d9ef45d6",
    "view-first.arrows": "a0dc208fa6fabe5c3193a9d8c5ef4b638d6f3150ef79e9ac8f24fe2f5fb30763",
    "view-first.parquet": "155ec74a833868260e39b04ecec3f54bb7cc2af4e91024e03111d1d516d9854c",
}
PINS = {
    "mixed": "faf4568226f8e0288a5c27a432c15711159d101170f87ec5805ddb9459b9b866",
    "required": "0fb3d6bd2aa895424d2cb723a0f25e84fc9f42b49a44b5a86d09b62a71441160",
    "empty-batch": "5c0b79381cefd1ca6cab338de728ca32596ddeb967865e4c1099292f8ede4a4f",
}


def messages(wire, count):
    with pa.BufferReader(wire) as carrier:
        records = list(pa.ipc.MessageReader.open_stream(carrier))
        assert [message.type for message in records] == ["schema"] + ["record batch"] * count
        assert all(message.metadata_version == pa.ipc.MetadataVersion.V5 for message in records)
        assert carrier.tell() == len(wire)


def observe_view_first(wire):
    with pa.BufferReader(wire) as carrier, pa.ipc.open_stream(carrier) as source:
        binary, integer = source.schema
        assert binary.type == pa.binary_view() and integer.type == pa.int32()
        fields = [(field.name, field.nullable) for field in source.schema]
        groups = []
        for batch in source:
            batch.validate(full=True)
            groups.append([column.to_pylist() for column in batch.columns])
        assert carrier.tell() == len(wire)
        assert wire.endswith(bytes.fromhex("ffffffff00000000"))
    return fields, groups


def view_first_inputs(out):
    stream = run_path(str(ARROW))["stream"]
    schema = pa.schema([
        pa.field("raw", pa.binary_view(), nullable=True),
        pa.field("count", pa.int32(), nullable=True),
    ])
    (out / "view-first.arrows").write_bytes(stream(schema, [
        ([None, b"", b"\xff\x00\x80"], [-2**31, None, 0]),
        ([], []),
        ([b"\x80abcdefghijklmno\x00", None], [2**31 - 1, -7]),
    ]))
    required = pa.schema([
        pa.field("raw", pa.binary_view(), nullable=False),
        pa.field("count", pa.int32(), nullable=True),
    ])
    (out / "view-first-empty.arrows").write_bytes(stream(required, [([], [])]))
    (out / "view-first-schema-only.arrows").write_bytes(stream(required, []))


def check_view_first(out):
    thrift = run_path(str(THRIFT))
    parquet = run_path(str(PARQUET))
    for name, counts in (("view-first", [3, 0, 2]), ("view-first-empty", [0])):
        source = (out / f"{name}.arrows").read_bytes()
        file = (out / f"{name}.parquet").read_bytes()
        wire = (out / f"{name}-returned.arrows").read_bytes()
        fields, groups = observe_view_first(source)
        assert [len(group[0]) for group in groups] == counts
        assert observe_view_first(wire) == (fields, groups)
        messages(source, len(groups))
        messages(wire, len(groups))
        parquet["check_wire_groups"](thrift, file, fields, groups, physical_order=(6, 1))
        parquet["check_arrow_groups"](file, fields, groups, physical_order=(6, 1))
    schema_only = (out / "view-first-schema-only.arrows").read_bytes()
    empty_fields, _ = observe_view_first((out / "view-first-empty.arrows").read_bytes())
    assert observe_view_first(schema_only) == (empty_fields, [])
    messages(schema_only, 0)
    for name, expected in VIEW_PINS.items():
        digest = sha256((out / name).read_bytes()).hexdigest()
        print(f"{digest}  {name}")
        assert digest == expected, f"{name}: fixture hash changed"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    out = parser.parse_args().out.resolve()
    assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
    assert version("thrift") == "0.25.0"
    subprocess.run([sys.executable, str(FORWARD), "--out", str(out)], cwd=ROOT, check=True)
    view_first_inputs(out)
    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
         "-DwarningAsError=true", "--run", str(HERE / "Return.lean"), str(out)],
        cwd=ROOT, check=True,
    )
    observe = run_path(str(FORWARD))["observe"]
    for name, counts in (("mixed", [3, 0, 2]), ("required", [2, 1]), ("empty-batch", [0])):
        source = (out / f"{name}.arrows").read_bytes()
        path = out / f"{name}-returned.arrows"
        wire = path.read_bytes()
        fields, groups = observe(source)
        assert [len(group[0]) for group in groups] == counts
        assert observe(wire) == (fields, groups)
        messages(source, len(groups))
        messages(wire, len(groups))
        digest = sha256(wire).hexdigest()
        print(f"{digest}  {path.name} {counts}")
        assert digest == PINS[name], f"{path.name}: returned carrier hash changed"
    check_view_first(out)
    print("PyArrow compared five IPC round trips through exact EOS.")
    print("PyArrow and Thrift confirmed BYTE_ARRAY-first leaves and chunks.")


if __name__ == "__main__":
    main()
