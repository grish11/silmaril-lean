"""Verify the checked-in fixture, or reproduce it with the pinned PyArrow wheel."""
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
MANIFEST = json.loads((HERE / "fixture.json").read_text(encoding="utf-8"))


def generate():
    import numpy as np
    import pyarrow as pa

    assert np.__version__ == MANIFEST["producer"]["numpy_version"]
    version = MANIFEST["producer"]["version"]
    assert pa.__version__ == pa.cpp_build_info.version == version
    schema = pa.schema([pa.field("n", pa.int32()), pa.field("téxt", pa.string())])
    batches = [
        pa.RecordBatch.from_arrays(
            [
                pa.array([row[field.name] for row in rows], type=field.type)
                for field in schema
            ],
            schema=schema,
        )
        for rows in MANIFEST["batches"]
    ]
    sink = pa.BufferOutputStream()
    options = pa.ipc.IpcWriteOptions(
        metadata_version=pa.ipc.MetadataVersion.V5, use_legacy_format=False, compression=None
    )
    with pa.ipc.new_stream(sink, schema, options=options) as stream:
        for batch in batches:
            stream.write_batch(batch)
    data = sink.getvalue().to_pybytes()
    with pa.ipc.open_stream(data) as stream:
        assert stream.schema == schema
        assert [batch.to_pylist() for batch in stream] == MANIFEST["batches"]
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--regenerate", action="store_true")
    args = parser.parse_args()
    path = HERE / MANIFEST["path"]
    data = generate() if args.regenerate else path.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    if digest != MANIFEST["sha256"]:
        raise SystemExit(f"{path.name}: unexpected SHA-256 {digest}")
    if args.regenerate:
        path.write_bytes(data)
    print(f"{path.name}: SHA-256 {digest}")


if __name__ == "__main__":
    main()
