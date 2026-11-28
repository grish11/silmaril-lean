"""Check both composed DATE conversions with pinned PyArrow and Thrift probes."""

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
    "optional_edges": (True, [[], [-(2**31), None], [], [2**31 - 1], []]),
    "required_edges": (False, [[], [-1, 0], []]),
    "all_empty": (True, [[], [], []]),
}

HARNESS = """module

meta import Silmaril.Formats.Parquet.Date.RoundTrip.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet

private meta def writerLimits : Date.FromIpc.Multi.Limits :=
  ⟨⟨1, 4096, {}, ⟨{}, 64, ⟨64, 256, ⟨16, 64⟩, 0⟩⟩⟩, 16, 32⟩

private meta def toParquet (input : KBytes) : IO Bytes :=
  match Date.FromIpc.Multi.convert {} writerLimits {} input with
  | .ok wire => pure wire
  | .error cause => throw (IO.userError (reprStr cause))

private meta def toArrow (input : Bytes) : IO KBytes :=
  match Date.Events.ToIpc.convert {} {} input with
  | .ok wire => pure wire
  | .error cause => throw (IO.userError (reprStr cause))

private meta def parquetCycle (directory : System.FilePath) (file : Bytes) : IO Unit := do
  let arrow ← toArrow file
  let output ← toParquet arrow
  IO.FS.writeBinFile (directory / "returned.arrow") arrow.toByteArray
  IO.FS.writeBinFile (directory / "returned.parquet") output.data

private meta def arrowCycle (directory : System.FilePath) (input : KBytes) : IO Unit := do
  let middle ← toParquet input
  IO.FS.writeBinFile (directory / "middle.parquet") middle.data
  parquetCycle directory middle

private meta def schemaOnly (directory : System.FilePath) (file : Bytes) : IO Unit := do
  let arrow ← toArrow file
  match Date.FromIpc.Multi.convert {} writerLimits {} arrow with
  | .error (.source (.batchCount 0)) =>
    IO.FS.writeBinFile (directory / "returned.arrow") arrow.toByteArray
  | _ => throw (IO.userError "Expected the schema-only refusal")
"""


def folder(root, label):
    directory = root / label
    directory.mkdir()
    return directory, json.dumps(str(directory))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pyarrow-path", type=Path)
    parser.add_argument("--thrift-path", type=Path)
    parser.add_argument("--regenerate", action="store_true", help="Write the observed fixture hashes")
    args = parser.parse_args()
    for path in (args.pyarrow_path, args.thrift_path):
        if path is not None:
            sys.path.insert(0, str(path.resolve()))

    import pyarrow as pa
    import pyarrow.parquet as pq
    from thrift.Thrift import TType
    from thrift.protocol.TCompactProtocol import TCompactProtocol
    from thrift.transport.TTransport import TMemoryBuffer

    multi_dir = ROOT / "scripts/date32-ipc-to-parquet-groups-oracle"
    multi_pin = json.loads((multi_dir / "fixtures.json").read_text(encoding="utf-8"))
    manifest = {key: multi_pin[key] for key in
                ("cpython", "pyarrow", "pyarrow_wheel_sha256", "thrift", "thrift_wheel_sha256", "lean_toolchain")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == manifest["pyarrow"]
    assert version("thrift") == manifest["thrift"]
    assert (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip() == manifest["lean_toolchain"]

    multi = runpy.run_path(str(multi_dir / "check.py"))
    producer = runpy.run_path(str(ROOT / "scripts/arrow-date32-writer-oracle/check.py"))
    parquet = runpy.run_path(str(ROOT / "scripts/parquet-date-oracle/check.py"))
    parquet["raw_leaf"].__globals__.update(pa=pa, pq=pq, TType=TType, TCompactProtocol=TCompactProtocol,
                                            TMemoryBuffer=TMemoryBuffer)
    page = runpy.run_path(str(ROOT / "scripts/parquet-scalar-page/PyArrowOracle.py"))
    describe = producer["hash_bytes"]
    manifest["cases"] = {}

    def observe_parquet(path, schema, batches):
        wire = path.read_bytes()
        multi["observe"](pa, pq, wire, schema, batches, parquet["raw_leaf"], page["header_fields"],
                         TCompactProtocol, TMemoryBuffer)
        return describe(wire)

    with tempfile.TemporaryDirectory(prefix="date-roundtrip-") as scratch:
        root = Path(scratch)
        commands = [HARNESS]
        schemas = {}
        for label, (nullable, batches) in CASES.items():
            schema, wire = producer["reference"](pa, "日付", nullable, batches)
            producer["observe"](pa, wire, schema, batches)
            schemas[label] = schema
            _, prefix = folder(root, label)
            commands.append(f"#eval arrowCycle {prefix} {multi['bytes_term'](wire)}")
            manifest["cases"][label] = {"field": "日付", "nullable": nullable, "batches": batches,
                                        "source_ipc": describe(wire)}

        # Reuse the independently pinned converted-only file with the original Thrift edit.
        days = parquet["EDGE_DAYS"]
        original = parquet["producer"](days, pa.date32(), True)
        legacy = parquet["with_annotations"](original, 6, None)
        parquet_pin = json.loads(parquet["MANIFEST"].read_text(encoding="utf-8"))
        legacy_pin = parquet_pin["fixtures"]["date_converted_only"]
        assert describe(legacy) == {key: legacy_pin[key] for key in ("bytes", "sha256")}
        assert parquet["raw_leaf"](legacy)[0] == legacy_pin["raw_schema_fields"]
        parquet["host_observation"]("converted_only", legacy, days, pa.date32(), 0)
        legacy_schema = pa.schema([pa.field("date", pa.date32(), nullable=True)])
        assert pq.ParquetFile(pa.BufferReader(legacy)).schema_arrow == legacy_schema
        _, prefix = folder(root, "converted_only")
        commands.append(f"#eval parquetCycle {prefix} {parquet['lean_bytes'](legacy)}")

        # Closing a writer before writing any groups makes a genuinely schema-only Parquet file.
        schema = pa.schema([pa.field("date", pa.date32(), nullable=False)])
        sink = pa.BufferOutputStream()
        with pq.ParquetWriter(sink, schema, compression="NONE", use_dictionary=False, store_schema=False):
            pass
        schema_only = sink.getvalue().to_pybytes()
        schema_file = pq.ParquetFile(pa.BufferReader(schema_only))
        assert schema_file.schema_arrow == schema and schema_file.num_row_groups == 0
        _, prefix = folder(root, "schema_only")
        commands.append(f"#eval schemaOnly {prefix} {parquet['lean_bytes'](schema_only)}")

        driver = root / "Probe.lean"
        driver.write_text("\n".join(commands) + "\n", encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(driver)], cwd=ROOT, check=True)

        for label, (_, batches) in CASES.items():
            directory = root / label
            returned = (directory / "returned.arrow").read_bytes()
            producer["observe"](pa, returned, schemas[label], batches)
            manifest["cases"][label].update(
                returned_ipc=describe(returned),
                middle_parquet=observe_parquet(directory / "middle.parquet", schemas[label], batches),
                returned_parquet=observe_parquet(directory / "returned.parquet", schemas[label], batches),
            )

        returned = (root / "converted_only" / "returned.arrow").read_bytes()
        producer["observe"](pa, returned, legacy_schema, [days])
        manifest["converted_only"] = {
            "source": describe(legacy), "provenance": legacy_pin["provenance"],
            "returned_ipc": describe(returned),
            "returned_parquet": observe_parquet(root / "converted_only" / "returned.parquet", legacy_schema, [days]),
        }
        returned = (root / "schema_only" / "returned.arrow").read_bytes()
        producer["observe"](pa, returned, schema, [])
        assert not (root / "schema_only" / "returned.parquet").exists()
        manifest["schema_only"] = {
            "source": describe(schema_only), "returned_ipc": describe(returned),
            "reverse_error": ".source (.batchCount 0)",
        }

    pin = HERE / "fixtures.json"
    if args.regenerate:
        pin.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    else:
        assert manifest == json.loads(pin.read_text(encoding="utf-8"))
        print("PASS three bidirectional probes, converted-only normalization, and zero-group refusal")


if __name__ == "__main__":
    main()
