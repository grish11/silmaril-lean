"""Reproduce the pinned checked BinaryView inputs and run the named import oracle."""

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


def emit(schema, batches):
    sink = pa.BufferOutputStream()
    opts = pa.ipc.IpcWriteOptions(metadata_version=pa.ipc.MetadataVersion.V5, compression=None)
    with pa.ipc.new_stream(sink, schema, options=opts) as writer:
        for batch in batches:
            writer.write_batch(batch)
    return sink.getvalue().to_pybytes()


def controls(directory):
    with pa.ipc.open_stream(directory / "reference.arrows") as reader:
        schema = reader.schema
        batches = list(reader)
    assert schema == pa.schema([pa.field("blob", pa.binary_view())])
    original = [batch.column(0).to_pylist() for batch in batches]
    assert list(map(len, original)) == [2, 0, 6]
    reordered = emit(schema, reversed(batches))
    with pa.ipc.open_stream(reordered) as reader:
        assert reader.schema == schema
        assert [batch.column(0).to_pylist() for batch in reader] == original[::-1]

    text_schema = pa.schema([pa.field("blob", pa.string_view())])
    text = pa.record_batch([pa.array(["x", None, ""], type=pa.string_view())], schema=text_schema)
    utf8 = emit(text_schema, [text])
    with pa.ipc.open_stream(utf8) as reader:
        assert reader.schema == text_schema and list(reader) == [text]
    return {"reordered.arrows": reordered, "utf8.arrows": utf8}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()
    directory = args.out.resolve()
    subprocess.run(
        [sys.executable, str(ROOT / "scripts/binary-file-observation-oracle/check.py"), "--out", str(directory)],
        cwd=ROOT, check=True,
    )
    assert pa.__version__ == "26.0.1"
    generated = controls(directory)
    pins = {name: sha256(wire).hexdigest() for name, wire in generated.items()}
    assert pins == json.loads((HERE / "sha256.json").read_text(encoding="utf-8")), pins
    for name, wire in generated.items():
        (directory / name).write_bytes(wire)
        print(f"{pins[name]}  {name}")
    fixtures = ("selected.parquet", "late-length-error.parquet", "reference.arrows", *generated)
    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
         "--run", str(HERE / "Check.lean"), *[str(directory / name) for name in fixtures]],
        cwd=ROOT, check=True,
    )


if __name__ == "__main__":
    main()
