"""Check selected named Date32 columns in native Parquet with PyArrow and Thrift."""

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
TESTS = ROOT / "Silmaril/Formats/Relational/NamedTable/Date32/Export/Tests.lean"


def lean_slot(value):
    return "none" if value is None else f"some (Int32.ofInt ({value}))"


def lean_string(value):
    return json.dumps(str(value), ensure_ascii=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pyarrow-path", type=Path)
    parser.add_argument("--thrift-path", type=Path)
    parser.add_argument("--regenerate", action="store_true", help="Update fixture fingerprints")
    args = parser.parse_args()
    for path in (args.pyarrow_path, args.thrift_path):
        if path is not None:
            sys.path.insert(0, str(path.resolve()))
    import pyarrow as pa
    import pyarrow.parquet as pq
    from thrift.Thrift import TType
    from thrift.protocol.TCompactProtocol import TCompactProtocol
    from thrift.transport.TTransport import TMemoryBuffer

    prior = ROOT / "scripts/parquet-date-csv-roundtrip-oracle"
    sources = runpy.run_path(str(prior / "check.py"))
    output = runpy.run_path(str(ROOT / "scripts/arrow-date32-to-parquet-oracle/check.py"))
    date_oracle = runpy.run_path(str(ROOT / "scripts/parquet-date-oracle/check.py"))
    page = runpy.run_path(str(ROOT / "scripts/parquet-scalar-page/PyArrowOracle.py"))
    raw_leaf = date_oracle["raw_leaf"]
    raw_leaf.__globals__.update(TType=TType, TCompactProtocol=TCompactProtocol, TMemoryBuffer=TMemoryBuffer)
    hash_bytes = runpy.run_path(str(ROOT / "scripts/arrow-date32-writer-oracle/check.py"))["hash_bytes"]
    prior_pin = json.loads((prior / "fixtures.json").read_text(encoding="utf-8"))
    pin = {key: prior_pin[key] for key in
           ("cpython", "pyarrow", "pyarrow_wheel_sha256", "thrift", "thrift_wheel_sha256", "lean_toolchain")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == pin["pyarrow"]
    assert version("thrift") == pin["thrift"]
    assert (ROOT / "lean-toolchain").read_text().strip() == pin["lean_toolchain"]

    imports = {
        "imported_optional": ("日付", True, [[-2147483648, None, -1], [11016, 2147483647, -1]]),
        "imported_empty_required": ("époque", False, []),
    }
    paired = [(-9, None), (0, 11016), (None, -719528), (3, 11016)]
    pin["cases"] = {}
    with tempfile.TemporaryDirectory(prefix="named-date32-parquet-") as temporary:
        folder = Path(temporary)
        commands = []
        expected = {}
        for case, (name, nullable, groups) in imports.items():
            schema = pa.schema([pa.field(name, pa.date32(), nullable=nullable)])
            wire = sources["source_file"](pa, pq, schema, groups)
            opened = pq.ParquetFile(pa.BufferReader(wire))
            assert opened.schema_arrow == schema
            assert opened.num_row_groups == len(groups)
            for index, group in enumerate(groups):
                actual = opened.read_row_group(index).column(0).combine_chunks()
                assert actual.view(pa.int32()).to_pylist() == group
            slots = [day for group in groups for day in group]
            expected[case] = (schema, slots)
            pin["cases"][case] = {"source_groups": groups, "source_parquet": hash_bytes(wire),
                                  "selected_index": 0, "signed_slots": slots}
            path = lean_string(folder / (case + ".parquet"))
            commands.append(f"#eval importAndEmit {path} {lean_string(name)} {str(nullable).lower()} "
                            f"{date_oracle['lean_bytes'](wire)}")
        case = "duplicate_labels_index_one"
        path = lean_string(folder / (case + ".parquet"))
        pairs = "[" + ", ".join(f"({lean_slot(first)}, {lean_slot(second)})" for first, second in paired) + "]"
        commands.append(f'#eval emit {path} (fromPairs {pairs}) ⟨1, "日付", true⟩')
        slots = [second for _, second in paired]
        expected[case] = (pa.schema([pa.field("日付", pa.date32(), nullable=True)]), slots)
        pin["cases"][case] = {"table_rows": paired, "selected_index": 1, "signed_slots": slots}

        harness = folder / "Oracle.lean"
        harness.write_text(TESTS.read_text(encoding="utf-8") + "\n" + "\n".join(commands) + "\n",
                           encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(harness)], cwd=ROOT, check=True)
        for case, (schema, slots) in expected.items():
            wire = (folder / (case + ".parquet")).read_bytes()
            leaf, body = output["observe_file"](pa, pq, wire, schema, slots, raw_leaf,
                                                page["header_fields"], TCompactProtocol, TMemoryBuffer)
            pin["cases"][case].update(lean_parquet=hash_bytes(wire), v1_body=hash_bytes(body),
                                      parquet_leaf=leaf)

    # JSON represents the ordered input pairs as arrays.
    pin["cases"]["duplicate_labels_index_one"]["table_rows"] = [list(pair) for pair in paired]
    manifest = HERE / "fixtures.json"
    if args.regenerate:
        manifest.write_text(json.dumps(pin, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    else:
        assert pin == json.loads(manifest.read_text(encoding="utf-8")), json.dumps(pin, indent=2)
    print(f"PASS {len(expected)} named Date32 exports with exact PyArrow/Thrift readback")


if __name__ == "__main__":
    main()
