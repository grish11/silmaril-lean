"""Verify the schema-only bridge with zero-group files from PyArrow and Lean."""

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
CASES = {"optional": ("日付", True), "required": ("époque", False)}

HARNESS = """module

meta import Silmaril.Formats.Parquet.Date.FromIpc.SchemaOnly.Defs
meta import Silmaril.Formats.Parquet.Date.Events.ToIpc.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Date.FromIpc.SchemaOnly

private meta def limits : Limits := ⟨4096, {}⟩

private meta def toParquet (target : System.FilePath) (source : KBytes) : IO Unit :=
  match convert {} limits {} source with
  | .ok file => IO.FS.writeBinFile target file.data
  | .error cause => throw (IO.userError (reprStr cause))

private meta def producerCycle (folder : System.FilePath) (source : Bytes) : IO Unit := do
  let .ok ipc := Date.Events.ToIpc.convert {} {} source
    | throw (IO.userError "Could not convert the PyArrow Parquet source")
  IO.FS.writeBinFile (folder / "from-source.arrow") ipc.toByteArray
  toParquet (folder / "from-source.parquet") ipc

private meta def rejects (writer : Limits) (source : KBytes) (cause : Date.FromIpc.Error) : Bool :=
  match convert {} writer {} source with
  | .ok _ => false
  | .error actual => actual == cause

private meta def tightFile (source : KBytes) : Bool :=
  match convert {} limits {} source with
  | .error _ => false
  | .ok file =>
    let exact := { limits with maxFileBytes := file.length }
    let short := { limits with maxFileBytes := file.length - 1 }
    match convert {} exact {} source with
    | .error _ => false
    | .ok exactFile => exactFile == file && rejects short source (.writer (.compact .byteLimit))
"""


def observe_parquet(pa, pq, wire, schema):
    parquet = pq.ParquetFile(pa.BufferReader(wire))
    assert parquet.schema_arrow == schema
    assert parquet.metadata.num_rows == parquet.metadata.num_row_groups == 0
    assert parquet.schema.column(0).physical_type == "INT32"
    assert str(parquet.schema.column(0).logical_type) == "Date"
    table = parquet.read()
    assert table.schema == schema and table.num_rows == 0


def check_raw(wire, schema, parquet, protocol_type, transport, tags):
    assert wire[:4] == wire[-4:] == b"PAR1"
    leaf, footer_start, _, _ = parquet["raw_leaf"](wire)
    field = schema[0]
    assert leaf == {"1": 1, "3": int(field.nullable), "4": field.name, "6": 6, "10": [[6, []]]}
    assert footer_start == 4
    memory = transport(wire[footer_start:-8])
    protocol = protocol_type(memory)
    values = {}
    for kind, field_id in parquet["fields"](protocol):
        if field_id == 1:
            assert kind == tags.I32
            values[1] = protocol.readI32()
        elif field_id == 2:
            protocol.skip(kind)
        elif field_id == 3:
            assert kind == tags.I64
            values[3] = protocol.readI64()
        elif field_id == 4:
            assert kind == tags.LIST
            element, count = protocol.readListBegin()
            assert (element, count) == (tags.STRUCT, 0)
            protocol.readListEnd()
            values[4] = count
        else:
            raise AssertionError(f"Unexpected emitted FileMetaData field {field_id}")
    assert values == {1: 1, 3: 0, 4: 0}
    assert memory.cstringio_buf.tell() == len(wire) - 12


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pyarrow-path", type=Path)
    parser.add_argument("--thrift-path", type=Path)
    parser.add_argument("--regenerate", action="store_true", help="Write fixture hashes")
    args = parser.parse_args()
    for path in (args.pyarrow_path, args.thrift_path):
        if path is not None:
            sys.path.insert(0, str(path.resolve()))

    import pyarrow as pa
    import pyarrow.parquet as pq
    from thrift.Thrift import TType
    from thrift.protocol.TCompactProtocol import TCompactProtocol
    from thrift.transport.TTransport import TMemoryBuffer

    parent = json.loads((ROOT / "scripts/date-roundtrip-oracle/fixtures.json").read_text(encoding="utf-8"))
    manifest = {key: parent[key] for key in
                ("cpython", "pyarrow", "pyarrow_wheel_sha256", "thrift", "thrift_wheel_sha256", "lean_toolchain")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == manifest["pyarrow"]
    assert version("thrift") == manifest["thrift"]
    assert (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip() == manifest["lean_toolchain"]
    producer = runpy.run_path(str(ROOT / "scripts/arrow-date32-writer-oracle/check.py"))
    parquet = runpy.run_path(str(ROOT / "scripts/parquet-date-oracle/check.py"))
    parquet["raw_leaf"].__globals__.update(TType=TType, TCompactProtocol=TCompactProtocol,
                                            TMemoryBuffer=TMemoryBuffer)
    describe = producer["hash_bytes"]
    bytes_term = runpy.run_path(str(ROOT / "scripts/arrow-date-stream-oracle/check.py"))["bytes_term"]
    manifest["cases"], manifest["controls"] = {}, {}

    with tempfile.TemporaryDirectory(prefix="parquet-date-schema-only-") as scratch:
        root = Path(scratch)
        commands = [HARNESS]
        inputs, schemas = {}, {}
        for label, (name, nullable) in CASES.items():
            schema, ipc = producer["reference"](pa, name, nullable, [])
            producer["observe"](pa, ipc, schema, [])
            sink = pa.BufferOutputStream()
            with pq.ParquetWriter(sink, schema, version="2.6", compression="NONE", store_schema=False):
                pass
            source = sink.getvalue().to_pybytes()
            observe_parquet(pa, pq, source, schema)
            assert parquet['raw_leaf'](source)[1] == 4
            inputs[label], schemas[label] = ipc, schema
            directory = root / label
            directory.mkdir()
            commands.append(f"#eval toParquet {json.dumps(str(directory / 'direct.parquet'))} {bytes_term(ipc)}")
            commands.append(f"#eval producerCycle {json.dumps(str(directory))} {parquet['lean_bytes'](source)}")
            manifest["cases"][label] = {"name": name, "nullable": nullable,
                                        "pyarrow_ipc": describe(ipc), "pyarrow_parquet": describe(source)}

        _, explicit_empty = producer["reference"](pa, "date", True, [[]])
        optional = inputs["optional"]
        assert optional[-8:] == b"\xff\xff\xff\xff\0\0\0\0"
        date64_sink = pa.BufferOutputStream()
        with pa.ipc.new_stream(date64_sink, pa.schema([pa.field("date", pa.date64())])):
            pass
        controls = {
            "explicit_empty": (explicit_empty, "limits", "(.batchCount 1)"),
            "date64": (date64_sink.getvalue().to_pybytes(), "limits", "(.wrongUnit .millisecond)"),
            "missing_eos": (optional[:-8], "{ limits with maxFileBytes := 0 }",
                            "(.reader (.batch 0 (.envelope (.malformed .truncated))))"),
        }
        for label, (wire, cap, cause) in controls.items():
            commands.append(f"#guard rejects {cap} {bytes_term(wire)} {cause}")
            manifest["controls"][label] = {"ipc": describe(wire), "writer": cap, "lean_error": cause}
        commands.append(f"#guard tightFile {bytes_term(optional)}")
        driver = root / "Fixtures.lean"
        driver.write_text("\n".join(commands) + "\n", encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(driver)], cwd=ROOT, check=True)

        for label, schema in schemas.items():
            directory = root / label
            ipc = (directory / "from-source.arrow").read_bytes()
            producer["observe"](pa, ipc, schema, [])
            manifest["cases"][label]["lean_ipc_from_parquet"] = describe(ipc)
            for file in ("direct", "from-source"):
                wire = (directory / f"{file}.parquet").read_bytes()
                observe_parquet(pa, pq, wire, schema)
                check_raw(wire, schema, parquet, TCompactProtocol, TMemoryBuffer, TType)
                manifest["cases"][label][f"lean_parquet_{file}"] = describe(wire)

    pin = HERE / "fixtures.json"
    if args.regenerate:
        pin.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    else:
        assert manifest == json.loads(pin.read_text(encoding="utf-8"))
        print("PASS two PyArrow zero-group producers, four Lean files, and four refusal/extent controls")


if __name__ == "__main__":
    main()
