"""Check Lean's Parquet DATE to IPC conversion with pinned PyArrow files."""

import argparse
from importlib.metadata import version
import json
import os
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
CASES = {
    "optional": (True, [[-(2**31), -1, None], [0, 11016, 2**31 - 1]]),
    "required": (False, [[-719528, -1, 0], [11016]]),
}

HARNESS = """module

meta import Silmaril.Formats.Parquet.Date.Events.ToIpc.Defs

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Date.Events.ToIpc

private meta def write (path : System.FilePath) (source : Bytes) : IO Unit := do
  match convert {} {} source with
  | .ok wire => IO.FS.writeBinFile path wire.toByteArray
  | .error cause => throw (IO.userError (reprStr cause))

private meta def rejects (limits : Arrow.ObservationLimits) (source : Bytes)
    (expected : Error) : Bool :=
  match convert {} limits source with
  | .ok _ => false
  | .error cause => cause == expected

private meta def originalOpenError (source : Bytes) : Bool :=
  match Date.Events.readAll {} source with
  | .ok _ => false
  | .error cause => rejects {} source (.source cause)

private meta def damagedPrefix (source : Bytes) : Bool :=
  match Date.Events.readAll {} source with
  | .error _ => false
  | .ok ⟨_, trace⟩ =>
    trace.batches.map (·.rowCount) == [4] &&
    decide (trace.termination = .readError (.groupFailure 1 (.scan .unsupportedPageEncoding)))
"""


def parquet_fixture(pa, pq, schema, groups):
    sink = pa.BufferOutputStream()
    values = pa.array([day for group in groups for day in group], type=pa.int32()).view(pa.date32())
    pq.write_table(pa.Table.from_arrays([values], schema=schema), sink,
                   version="2.6", data_page_version="1.0", row_group_size=3,
                   compression="NONE", use_dictionary=False, write_statistics=False,
                   store_schema=False)
    wire = sink.getvalue().to_pybytes()
    parquet = pq.ParquetFile(pa.BufferReader(wire))
    assert parquet.schema_arrow == schema
    assert parquet.schema.column(0).physical_type == "INT32"
    assert str(parquet.schema.column(0).logical_type) == "Date"
    observed = [
        parquet.read_row_group(index).column(0).combine_chunks().view(pa.int32()).to_pylist()
        for index in range(parquet.num_row_groups)
    ]
    assert observed == groups
    return wire


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pyarrow-path", type=Path)
    parser.add_argument("--thrift-path", type=Path)
    parser.add_argument("--regenerate", action="store_true", help="Write pinned reference observations")
    args = parser.parse_args()
    for path in (args.pyarrow_path, args.thrift_path):
        if path is not None:
            sys.path.insert(0, str(path.resolve()))

    import pyarrow as pa
    import pyarrow.parquet as pq
    from thrift.Thrift import TType
    from thrift.protocol.TCompactProtocol import TCompactProtocol
    from thrift.transport.TTransport import TMemoryBuffer

    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"

    writer = runpy.run_path(str(ROOT / "scripts/arrow-date32-writer-oracle/check.py"))
    parquet = runpy.run_path(str(ROOT / "scripts/parquet-date-oracle/check.py"))
    parquet["producer"].__globals__.update(
        pa=pa, pq=pq, TType=TType, TCompactProtocol=TCompactProtocol, TMemoryBuffer=TMemoryBuffer
    )
    source = parquet["producer"](parquet["EDGE_DAYS"], pa.date32(), True, group_size=4)
    damaged, offset = parquet["damage_second_group"](source)
    source_manifest = json.loads(parquet["MANIFEST"].read_text(encoding="utf-8"))
    damage_pin = source_manifest["event_fixtures"]["date_second_group_damaged"]
    assert {**writer["hash_bytes"](damaged), "offset": offset} == {
        key: damage_pin[key] for key in ("bytes", "sha256", "offset")
    }

    manifest = {
        "cpython": "3.13.5", "pyarrow": pa.__version__, "thrift": version("thrift"),
        "late_failure": damage_pin,
        "cases": {},
    }
    with tempfile.TemporaryDirectory(prefix="parquet-date-to-ipc-") as scratch:
        root = Path(scratch)
        lean = [HARNESS]
        for label, (nullable, groups) in CASES.items():
            name = "日付"
            schema, reference = writer["reference"](pa, name, nullable, groups)
            writer["observe"](pa, reference, schema, groups)
            source = parquet_fixture(pa, pq, schema, groups)
            manifest["cases"][label] = {
                "field": name, "nullable": nullable, "groups": groups,
                "parquet": writer["hash_bytes"](source),
                "ipc_reference": writer["hash_bytes"](reference),
            }
            lean.append(f"#eval write {json.dumps(str(root / (label + '.arrow')))} "
                        f"{parquet['lean_bytes'](source)}")

        bad = parquet["lean_bytes"](damaged)
        cause = "(.source (.groupFailure 1 (.scan .unsupportedPageEncoding)))"
        lean += [
            f"#guard damagedPrefix {bad}",
            f"#guard rejects {{}} {bad} {cause}",
            f"#guard rejects {{ ipc := {{ batches := 0 }} }} {bad} {cause}",
            f"#guard originalOpenError {parquet['lean_bytes'](b'')}",
        ]

        pin = HERE / "fixtures.json"
        if args.regenerate:
            pin.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
            return
        assert manifest == json.loads(pin.read_text(encoding="utf-8"))
        driver = root / "Fixtures.lean"
        driver.write_text("\n".join(lean) + "\n", encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(driver)], cwd=ROOT, check=True)
        for label, (nullable, groups) in CASES.items():
            schema = pa.schema([pa.field("日付", pa.date32(), nullable=nullable)])
            wire = (root / f"{label}.arrow").read_bytes()
            writer["observe"](pa, wire, schema, groups)
            messages = list(pa.ipc.MessageReader.open_stream(wire))
            assert len(messages) == 1 + len(groups)
            writer["checked_day_schema"](messages[0].metadata.to_pybytes())
            for message, slots in zip(messages[1:], groups, strict=True):
                writer["check_record"](message, slots)
    print("PASS two Parquet-to-IPC cases, four record bodies, and original source-error controls")


if __name__ == "__main__":
    main()
