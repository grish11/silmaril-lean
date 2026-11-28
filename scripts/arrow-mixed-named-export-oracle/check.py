"""Check five pinned Lean-emitted mixed IPC streams with PyArrow."""

import argparse
from hashlib import sha256
import os
from pathlib import Path
import subprocess
import sys

import pyarrow as pa


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
EOS = bytes.fromhex("ffffffff00000000")
PINS = {
    "empty-batch": "5c0b79381cefd1ca6cab338de728ca32596ddeb967865e4c1099292f8ede4a4f",
    "empty-middle": "019924d4ecd941947876755ed7b4ebc669cbd73488e2b8f7024ad1af302e66c0",
    "rechunked": "765c863b63b7d970b658423dc50772a6c2feb3bec947ff5cf029bc5a86f1fe9a",
    "reversed": "642f994357e81cabce1d69851c509f38745d5c5736b390a794af4df14df27aa0",
    "schema-only": "39f9b01681188ecf956581ddb02abf34fd7f41e58aebc1c0a45e5dd02862cc75",
}


def check(path, schema, groups):
    data = path.read_bytes()
    digest = sha256(data).hexdigest()
    print(f"{digest}  {path.name} (batches {[len(group) for group in groups]})")
    assert digest == PINS[path.stem], f"{path.name}: fixture hash changed"
    assert data.endswith(EOS)
    with pa.BufferReader(data) as carrier, pa.ipc.open_stream(carrier) as reader:
        assert reader.schema.equals(schema)
        batches = list(reader)
        for batch in batches:
            batch.validate(full=True)
        assert [list(zip(*(column.to_pylist() for column in batch.columns), strict=True))
                for batch in batches] == groups
        assert carrier.tell() == len(data)
    with pa.BufferReader(data) as carrier:
        messages = list(pa.ipc.MessageReader.open_stream(carrier))
        assert [message.type for message in messages] == ["schema"] + ["record batch"] * len(groups)
        assert all(message.metadata_version == pa.ipc.MetadataVersion.V5 for message in messages)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    out = parser.parse_args().out.resolve()
    if pa.__version__ != "26.0.1" or sys.byteorder != "little":
        raise SystemExit("fixture requires little-endian PyArrow 26.0.1")
    out.mkdir(parents=True, exist_ok=True)
    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
         "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(out)],
        cwd=ROOT, check=True,
    )
    ordered = pa.schema([pa.field("ordinal", pa.int32()), pa.field("payload", pa.binary_view())])
    reversed_schema = pa.schema([pa.field("raw", pa.binary_view()),
                                 pa.field("value", pa.int32(), nullable=False)])
    after = [(2**31 - 1, b"\xff\x00\x01" + b"q" * 16), (0, b"\x00\xff")]
    rows = [(-2**31, b""), (None, None), *after]
    reverse = [(binary, integer) for integer, binary in [rows[0], (7, None), *after]]
    for name, schema, groups in [
        ("empty-middle", ordered, [rows[:2], [], rows[2:]]),
        ("rechunked", ordered, [rows]),
        ("reversed", reversed_schema, [reverse[:1], reverse[1:]]),
        ("schema-only", ordered, []),
        ("empty-batch", ordered, [[]]),
    ]:
        check(out / f"{name}.arrows", schema, groups)


if __name__ == "__main__":
    main()
