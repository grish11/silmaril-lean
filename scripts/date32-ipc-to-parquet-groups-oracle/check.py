"""Verify every group in the Lean-emitted multibatch Parquet DATE files."""

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
CASES = {
    "optional_middle_empty": ("日付", True, [[-(2**31), None, -1], [], [0, 11016, 2**31 - 1]]),
    "required_outer_empty": ("époque", False, [[], [-719528, -1], [0], []]),
    "all_empty": ("empty groups", True, [[] for _ in range(15)]),
}

HARNESS = """module

meta import Silmaril.Formats.Parquet.Date.FromIpc.Multi.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Date.FromIpc.Multi

private meta def limits : Limits := ⟨⟨1, 4096, {}, ⟨{}, 64, ⟨64, 256, ⟨16, 64⟩, 0⟩⟩⟩, 16, 32⟩

private meta def emit (path : System.FilePath) (input : KBytes) : IO Unit :=
  match convert {} limits {} input with
  | .ok wire => IO.FS.writeBinFile path wire.data
  | .error cause => throw (IO.userError (reprStr cause))

private meta def rejects (writer : Limits) (reader : Date.Limits) (input : KBytes)
    (expected : Error) : Bool :=
  match convert {} writer reader input with
  | .ok _ => false
  | .error cause => cause == expected

private meta def tightFile (input : KBytes) : Bool :=
  match convert {} limits {} input with
  | .error _ => false
  | .ok wire =>
    let exact := { limits with writer.maxFileBytes := wire.length }
    let short := { limits with writer.maxFileBytes := wire.length - 1 }
    match convert {} exact {} input with
    | .error _ => false
    | .ok exactWire => exactWire == wire && rejects short {} input (.footer .byteLimit)
"""


def bytes_term(data):
    width = 64
    chunks = [int.from_bytes(data[start:start + width], "little")
              for start in range(0, len(data), width)]
    return f"(KBytes.ofChunks {width} {len(data)} {chunks})"


def check_truncated_tail(pa, wire, expected_prefix):
    with pa.ipc.open_stream(wire) as reader:
        for slots in expected_prefix:
            batch = reader.read_next_batch()
            assert batch.column(0).view(pa.int32()).to_pylist() == slots
        try:
            reader.read_next_batch()
        except (pa.ArrowInvalid, OSError):
            return
    raise AssertionError("PyArrow accepted the truncated final record body")


def observe(pa, pq, wire, schema, batches, raw_leaf, header_fields, protocol, transport):
    field = schema[0]
    assert wire[:4] == wire[-4:] == b"PAR1"
    leaf, footer_start, _, _ = raw_leaf(wire)
    assert leaf == {"1": 1, "3": int(field.nullable), "4": field.name, "6": 6, "10": [[6, []]]}
    file = pq.ParquetFile(pa.BufferReader(wire))
    assert file.schema_arrow == schema
    assert file.schema.column(0).physical_type == "INT32"
    assert str(file.schema.column(0).logical_type) == "Date"
    assert file.metadata.num_row_groups == len(batches)
    assert file.metadata.num_rows == sum(map(len, batches))

    cursor = 4
    pages = []
    for index, slots in enumerate(batches):
        group = file.read_row_group(index)
        assert group.schema == schema and group.num_rows == len(slots)
        assert group.column(0).combine_chunks().view(pa.int32()).to_pylist() == slots

        metadata = file.metadata.row_group(index)
        chunk = metadata.column(0)
        assert metadata.num_rows == chunk.num_values == len(slots)
        assert chunk.compression == "UNCOMPRESSED" and chunk.dictionary_page_offset is None
        assert chunk.data_page_offset == cursor
        stop = cursor + chunk.total_compressed_size
        assert cursor < stop <= footer_start
        section = transport(wire[cursor:stop])
        header = header_fields(protocol(section), (5,))
        body = wire[cursor + section.cstringio_buf.tell():stop]
        assert header == {1: 0, 2: len(body), 3: len(body), 5: {1: len(slots), 2: 0, 3: 3, 4: 3}}
        words = b"".join(struct.pack("<i", day) for day in slots if day is not None)
        if field.nullable:
            definitions = b"".join(bytes((2, int(day is not None))) for day in slots)
            assert body == struct.pack("<I", len(definitions)) + definitions + words
        else:
            assert body == words
        pages.append((cursor, stop, body))
        cursor = stop
    assert cursor == footer_start
    return pages


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pyarrow-path", type=Path)
    parser.add_argument("--thrift-path", type=Path)
    parser.add_argument("--regenerate", action="store_true", help="Write independently observed fixture hashes")
    args = parser.parse_args()
    for path in (args.pyarrow_path, args.thrift_path):
        if path is not None:
            sys.path.insert(0, str(path.resolve()))
    import pyarrow as pa
    import pyarrow.parquet as pq
    from thrift.Thrift import TType
    from thrift.protocol.TCompactProtocol import TCompactProtocol
    from thrift.transport.TTransport import TMemoryBuffer

    parent = json.loads((ROOT / "scripts/arrow-date32-to-parquet-oracle/fixtures.json").read_text())
    manifest = {key: parent[key] for key in
                ("cpython", "pyarrow", "pyarrow_wheel_sha256", "thrift", "thrift_wheel_sha256", "lean_toolchain")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == manifest["pyarrow"]
    assert version("thrift") == manifest["thrift"]
    assert (ROOT / "lean-toolchain").read_text().strip() == manifest["lean_toolchain"]
    producer = runpy.run_path(str(ROOT / "scripts/arrow-date32-writer-oracle/check.py"))
    parquet = runpy.run_path(str(ROOT / "scripts/parquet-date-oracle/check.py"))
    parquet["raw_leaf"].__globals__.update(TType=TType, TCompactProtocol=TCompactProtocol,
                                            TMemoryBuffer=TMemoryBuffer)
    page = runpy.run_path(str(ROOT / "scripts/parquet-scalar-page/PyArrowOracle.py"))
    describe = producer["hash_bytes"]

    manifest["cases"], manifest["controls"] = {}, {}
    with tempfile.TemporaryDirectory(prefix="date32-ipc-to-parquet-groups-") as directory:
        root = Path(directory)
        source = {}
        schemas = {}
        commands = [HARNESS]
        for label, (name, nullable, batches) in CASES.items():
            schema, wire = producer["reference"](pa, name, nullable, batches)
            producer["observe"](pa, wire, schema, batches)
            source[label], schemas[label] = wire, schema
            output = json.dumps(str(root / f"{label}.parquet"))
            commands.append(f"#eval emit {output} {bytes_term(wire)}")
            manifest["cases"][label] = {"field": name, "nullable": nullable, "batches": batches,
                                        "pyarrow_ipc": describe(wire)}

        _, schema_only = producer["reference"](pa, "date", True, [])
        optional = source["optional_middle_empty"]
        required = source["required_outer_empty"]
        assert optional[-8:] == b"\xff\xff\xff\xff\0\0\0\0"
        truncated = optional[:-9]
        check_truncated_tail(pa, truncated, CASES["optional_middle_empty"][2][:-1])
        controls = [
            ("schema_only", schema_only, "limits", "{}", "(.source (.batchCount 0))"),
            ("missing_eos", optional[:-8], "{ limits with maxGroups := 0 }", "{}",
             "(.source (.reader (.batch 3 (.envelope (.malformed .truncated)))))"),
            ("late_body", truncated, "{ limits with maxGroups := 0 }", "{}",
             "(.source (.reader (.batch 2 (.body (.malformed .truncated)))))"),
            ("late_readback", required, "limits", "{ scan := { maxRows := 1 } }",
             "(.groupReadback 1 (.scan .rowLimit))"),
            ("group_cap", source["all_empty"], "{ limits with maxGroups := 14 }", "{}", ".groupLimit"),
            ("aggregate_rows", optional, "{ limits with maxTotalRows := 5 }", "{}", ".totalRows"),
        ]
        for label, wire, writer, reader, error in controls:
            commands.append(f"#guard rejects {writer} {reader} {bytes_term(wire)} {error}")
            manifest["controls"][label] = {"ipc": describe(wire), "writer": writer,
                                           "reader": reader, "lean_error": error}
        commands.append(f"#guard tightFile {bytes_term(optional)}")
        driver = root / "Fixtures.lean"
        driver.write_text("\n".join(commands) + "\n", encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(driver)], cwd=ROOT, check=True)
        for label, (_, _, batches) in CASES.items():
            wire = (root / f"{label}.parquet").read_bytes()
            pages = observe(pa, pq, wire, schemas[label], batches, parquet["raw_leaf"],
                            page["header_fields"], TCompactProtocol, TMemoryBuffer)
            manifest["cases"][label].update(lean_parquet=describe(wire),
                groups=[{"start": start, "stop": stop, "body": describe(body)}
                        for start, stop, body in pages])

    pin = HERE / "fixtures.json"
    if args.regenerate:
        pin.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    else:
        assert manifest == json.loads(pin.read_text(encoding="utf-8"))
        count = sum(len(batches) for _, _, batches in CASES.values())
        print(f"PASS {len(CASES)} files, {count} exact groups and seven refusal/extent controls")


if __name__ == "__main__":
    main()
