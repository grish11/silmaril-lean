"""Pin independent PyArrow V5 streams and compare their records to Lean inserts."""

import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys

import pyarrow as pa


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
EOS = b"\xff" * 4 + b"\x00" * 4

PINS = {
    "mixed": "2cc9db7f917f4eb58b8f5835f2494699a127d7adc0b6171a5430fcc8170c4ea7",
    "reverse": "8a4312128d3f62853df67b1faeb7128849d28dd8ade323ae1dd26761c79ca101",
    "schema-only": "d0adccd850bdcf0ae4bbe047774e448f0de64145d3d927e0e3e8af060c43eed6",
    "empty-batch": "f7882c3bb921b9f74c9622735aae1b88da7ce42858d0bf2ed69d4500a540af63",
    "unsupported": "063a1ea69fe3a8ff1b9eed9b2edccc21fb1e90b34b6fb5ccb82fbfce895f1441",
    "missing-eos": "e98ff52f689e8190dc072aa74660793f55d9bb16d6f355052fad49d57acf0b27",
    "late-body": "b37a9b72f4498d4491348ed6ab7de2a5cebaf438959f293873b5240f4f6aa283",
}


def stream(schema, records):
    sink = pa.BufferOutputStream()
    options = pa.ipc.IpcWriteOptions(metadata_version=pa.ipc.MetadataVersion.V5,
                                     use_legacy_format=False, compression=None)
    with pa.ipc.new_stream(sink, schema, options=options) as writer:
        for columns in records:
            arrays = [pa.array(values, type=field.type)
                      for values, field in zip(columns, schema, strict=True)]
            writer.write_batch(pa.record_batch(arrays, schema=schema))
    return sink.getvalue().to_pybytes()


def observe(wire):
    with pa.BufferReader(wire) as carrier, pa.ipc.open_stream(carrier) as reader:
        fields = [[field.name, field.nullable, str(field.type)] for field in reader.schema]
        batches = []
        for batch in reader:
            batch.validate(full=True)
            batches.append([
                [list(value) if isinstance(value, bytes) else value for value in row]
                for row in zip(*(column.to_pylist() for column in batch.columns), strict=True)
            ])
        assert wire.endswith(EOS) and carrier.tell() == len(wire)
    return {"fields": fields, "counts": list(map(len, batches)),
            "rows": [row for batch in batches for row in batch]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    out = parser.parse_args().out.resolve()
    if sys.byteorder != "little" or pa.__version__ != "26.0.1":
        raise SystemExit("fixture requires little-endian PyArrow 26.0.1")
    out.mkdir(parents=True, exist_ok=True)
    integer = pa.field("ordinal", pa.int32(), nullable=True)
    binary = pa.field("payload", pa.binary_view(), nullable=True)
    schema = pa.schema([integer, binary])
    reverse = pa.schema([binary, integer.with_nullable(False)])
    opaque = b"\xff\x00abcdefghijklmnop"
    streams = {
        "mixed": stream(schema, [
            ([-2**31, None, 0], [b"", None, b"\x00"]),
            ([], []),
            ([2**31 - 1, 0], [opaque, b"\x00"]),
        ]),
        "reverse": stream(reverse, [
            ([opaque, b"\x00"], [2**31 - 1, 0]),
            ([b"", None, b"\x00"], [-2**31, 7, 0]),
        ]),
        "schema-only": stream(schema, []),
        "empty-batch": stream(schema, [([], [])]),
        "unsupported": stream(pa.schema([integer, pa.field("payload", pa.string_view())]), []),
    }
    streams["missing-eos"] = streams["mixed"][:-len(EOS)]
    streams["late-body"] = streams["mixed"][:-len(EOS) - 1]
    for name, wire in streams.items():
        digest = sha256(wire).hexdigest()
        print(f"{digest}  {name}.arrows", flush=True)
        assert digest == PINS[name], f"{name}: fixture hash changed"
        (out / f"{name}.arrows").write_bytes(wire)
    expected = [observe(streams[name]) for name in ("mixed", "reverse", "schema-only", "empty-batch")]
    assert [value["counts"] for value in expected] == [[3, 0, 2], [2, 3], [], [0]]
    with pa.ipc.open_stream(streams["late-body"]) as reader:
        assert [reader.read_next_batch().num_rows, reader.read_next_batch().num_rows] == [3, 0]
        try:
            reader.read_next_batch()
        except (OSError, pa.ArrowInvalid):
            pass
        else:
            raise AssertionError("PyArrow accepted the truncated last batch")
    result = subprocess.check_output(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
         "-DwarningAsError=true", "--run", str(HERE / "Check.lean"), str(out)],
        cwd=ROOT, text=True,
    )
    assert json.loads(result) == expected
    print("Four PyArrow comparisons of exact named-table fields, batch counts and flattened nullable rows.")


if __name__ == "__main__":
    main()
