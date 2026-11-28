"""Read native Lean Parquet DATE files with pinned PyArrow and Apache Thrift."""

import argparse
from importlib.metadata import version
import json
import os
from pathlib import Path
import runpy
import struct
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
MANIFEST = HERE / "fixtures.json"
CASES = {
    "optional": ("日付", True, [-(2**31), None, -1, 0, 11016, 2**31 - 1]),
    "required": ("époque", False, [-719528, -1, 0, 11016]),
    "empty_required": ("empty required", False, []),
    "empty_optional": ("empty optional", True, []),
}

HARNESS = """module

meta import Silmaril.Formats.Parquet.Date.FromIpc.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Date.FromIpc

private meta def limits : FlatInt32Writer.Limits :=
  ⟨1, 4096, {}, ⟨{}, 64, ⟨64, 256, ⟨16, 64⟩, 0⟩⟩⟩

private meta def write (path : System.FilePath) (input : KBytes) : IO Unit :=
  match convert {} limits {} input with
  | .ok wire => IO.FS.writeBinFile path wire.data
  | .error error => throw (IO.userError (reprStr error))

private meta def rejects (input : KBytes) (expected : Error) : Bool :=
  match convert {} limits {} input with
  | .error actual => actual == expected
  | .ok _ => false
"""


def ipc_stream(pa, schema, columns):
    sink = pa.BufferOutputStream()
    with pa.ipc.new_stream(sink, schema) as writer:
        if columns is not None:
            writer.write_batch(pa.RecordBatch.from_arrays(columns, schema=schema))
    return sink.getvalue().to_pybytes()


def controls(pa, reference, valid):
    _, no_batches = reference(pa, "date", True, [])
    _, two_batches = reference(pa, "date", True, [[-1, None], []])
    schema64 = pa.schema([pa.field("date64", pa.date64())])
    whole_day = pa.array([-86400000, None, 0], type=pa.int64()).view(pa.date64())
    fractional_day = pa.array([-1], type=pa.int64()).view(pa.date64())
    required = pa.schema([pa.field("required", pa.date32(), nullable=False)])
    required_null = pa.array([None], type=pa.int32()).view(pa.date32())
    assert valid[-8:] == b"\xff\xff\xff\xff\0\0\0\0"
    return {
        "schema_only": (no_batches, "(.batchCount 0)"),
        "two_batches": (two_batches, "(.batchCount 2)"),
        "missing_eos": (valid[:-8], "(.reader (.batch 1 (.envelope (.malformed .truncated))))"),
        "date64": (ipc_stream(pa, schema64, [whole_day]), "(.wrongUnit .millisecond)"),
        "fractional_date64": (
            ipc_stream(pa, schema64, [fractional_day]), "(.reader (.batch 0 (.values (.nonWholeDay 0))))"
        ),
        "two_fields": (
            ipc_stream(pa, pa.schema([pa.field("a", pa.date32()), pa.field("b", pa.date32())]), None),
            "(.reader (.fieldCount 2))",
        ),
        "required_null": (
            ipc_stream(pa, required, [required_null]),
            "(.reader (.batch 0 (.values (.ipc (.malformed .validityBitmap)))))",
        ),
    }


def observe_file(pa, pq, wire, schema, slots, raw_leaf, header_fields, protocol, transport):
    name, nullable = schema[0].name, schema[0].nullable
    assert wire[:4] == wire[-4:] == b"PAR1"
    leaf, footer_start, _, _ = raw_leaf(wire)
    assert leaf == {"1": 1, "3": int(nullable), "4": name, "6": 6, "10": [[6, []]]}

    parquet = pq.ParquetFile(pa.BufferReader(wire))
    assert parquet.schema_arrow == schema
    assert parquet.metadata.num_row_groups == 1
    assert parquet.metadata.num_rows == len(slots)
    assert parquet.schema.column(0).physical_type == "INT32"
    assert str(parquet.schema.column(0).logical_type) == "Date"
    group = parquet.read_row_group(0)
    assert group.schema == schema and group.num_rows == len(slots)
    assert group.column(0).combine_chunks().view(pa.int32()).to_pylist() == slots

    chunk = parquet.metadata.row_group(0).column(0)
    assert chunk.compression == "UNCOMPRESSED" and chunk.num_values == len(slots)
    assert chunk.dictionary_page_offset is None and chunk.data_page_offset == 4
    assert 4 + chunk.total_compressed_size == footer_start
    section = transport(wire[4:footer_start])
    header = header_fields(protocol(section), (5,))
    body = wire[4 + section.cstringio_buf.tell():footer_start]
    assert header == {1: 0, 2: len(body), 3: len(body), 5: {1: len(slots), 2: 0, 3: 3, 4: 3}}
    words = b"".join(struct.pack("<i", day) for day in slots if day is not None)
    if nullable:
        definitions = b"".join(bytes((2, int(day is not None))) for day in slots)
        assert body == struct.pack("<I", len(definitions)) + definitions + words
    else:
        assert body == words
    return leaf, body


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pyarrow-path", type=Path)
    parser.add_argument("--thrift-path", type=Path)
    parser.add_argument("--regenerate", action="store_true", help="Write the exact fixture hashes")
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
    assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
    assert version("thrift") == "0.25.0"
    writer = runpy.run_path(str(ROOT / "scripts/arrow-date32-writer-oracle/check.py"))
    bytes_term = runpy.run_path(str(ROOT / "scripts/arrow-date-stream-oracle/check.py"))["bytes_term"]
    parquet = runpy.run_path(str(ROOT / "scripts/parquet-date-oracle/check.py"))
    parquet["raw_leaf"].__globals__.update(TType=TType, TCompactProtocol=TCompactProtocol,
                                            TMemoryBuffer=TMemoryBuffer)
    page = runpy.run_path(str(ROOT / "scripts/parquet-scalar-page/PyArrowOracle.py"))
    producer_pin = json.loads(parquet["MANIFEST"].read_text(encoding="utf-8"))
    manifest = {key: producer_pin[key] for key in
                ("cpython", "pyarrow", "pyarrow_wheel_sha256", "thrift", "thrift_wheel_sha256")}
    manifest["lean_toolchain"] = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    manifest["cases"] = {}
    manifest["controls"] = {}

    describe = writer["hash_bytes"]
    with tempfile.TemporaryDirectory(prefix="date32-to-parquet-") as directory:
        root = Path(directory)
        schemas = {}
        references = {}
        commands = [HARNESS]
        for label, (name, nullable, slots) in CASES.items():
            schema, reference = writer["reference"](pa, name, nullable, [slots])
            writer["observe"](pa, reference, schema, [slots])
            schemas[label], references[label] = schema, reference
            output = json.dumps(str(root / f"{label}.parquet"))
            commands.append(f"#eval write {output} {bytes_term(reference)}")
            manifest["cases"][label] = {"field": name, "nullable": nullable, "signed_slots": slots,
                                        "pyarrow_ipc": describe(reference)}

        for label, (wire, cause) in controls(pa, writer["reference"], references["optional"]).items():
            commands.append(f"#guard rejects {bytes_term(wire)} {cause}")
            manifest["controls"][label] = {"ipc": describe(wire), "lean_error": cause}
        driver = root / "Fixtures.lean"
        driver.write_text("\n".join(commands) + "\n", encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(driver)], cwd=ROOT, check=True)
        for label, (_, _, slots) in CASES.items():
            wire = (root / f"{label}.parquet").read_bytes()
            leaf, body = observe_file(pa, pq, wire, schemas[label], slots, parquet["raw_leaf"],
                                      page["header_fields"], TCompactProtocol, TMemoryBuffer)
            manifest["cases"][label].update(lean_parquet=describe(wire), v1_body=describe(body),
                                            parquet_leaf=leaf)

    if args.regenerate:
        MANIFEST.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    else:
        assert manifest == json.loads(MANIFEST.read_text(encoding="utf-8"))
        print(f"PASS {len(CASES)} Lean-emitted DATE files and {len(manifest['controls'])} refusal controls")


if __name__ == "__main__":
    main()
