"""Compare native Parquet DATE normalization through typed CSV with pinned tools."""

import argparse
import csv
import io
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
TESTS = ROOT / "Silmaril/Formats/Parquet/Date/RoundTrip/ViaCsv/Tests.lean"
LABEL = "日付"
CASES = {
    "cuts_a": [[-719528, None], [-1, 11016, 2932896]],
    "cuts_b": [[-719528], [None, -1, 11016], [2932896]],
    "mixed_empty": [[], [-719528], [], [], [None, -1], [11016, 2932896], []],
    "moved_null": [[None, -719528], [-1, 11016, 2932896]],
    "reordered_days": [[2932896, None], [-1, 11016, -719528]],
    "zero_groups": [],
    "empty_groups": [[], []],
}
NATIVE_EMPTY_CASES = ("mixed_empty", "empty_groups")


def source_file(pa, pq, schema, groups):
    with pa.BufferOutputStream() as sink:
        with pq.ParquetWriter(sink, schema, version="2.6", data_page_version="1.0",
                              compression="NONE", use_dictionary=False, write_statistics=False,
                              store_schema=False) as writer:
            for group in groups:
                column = pa.array(group, type=pa.int32()).view(pa.date32())
                writer.write_table(pa.Table.from_arrays([column], schema=schema))
        return sink.getvalue().to_pybytes()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pyarrow-path", type=Path)
    parser.add_argument("--thrift-path", type=Path)
    parser.add_argument("--regenerate", action="store_true", help="Update exact fixture fingerprints")
    args = parser.parse_args()
    for path in (args.pyarrow_path, args.thrift_path):
        if path is not None:
            sys.path.insert(0, str(path.resolve()))
    import pyarrow as pa
    import pyarrow.compute as pc
    import pyarrow.parquet as pq
    from thrift.Thrift import TType
    from thrift.protocol.TCompactProtocol import TCompactProtocol
    from thrift.transport.TTransport import TMemoryBuffer

    csv_tools = runpy.run_path(str(ROOT / "scripts/date32-from-csv-oracle/check.py"))
    emitted = runpy.run_path(str(ROOT / "scripts/arrow-date32-to-parquet-oracle/check.py"))
    native = runpy.run_path(str(ROOT / "scripts/parquet-date-oracle/check.py"))
    generator = runpy.run_path(str(ROOT / "scripts/date32-ipc-to-parquet-groups-oracle/check.py"))
    ipc = runpy.run_path(str(ROOT / "scripts/arrow-date32-writer-oracle/check.py"))
    pages = runpy.run_path(str(ROOT / "scripts/parquet-scalar-page/PyArrowOracle.py"))
    native["raw_leaf"].__globals__.update(pa=pa, pq=pq, TType=TType, TCompactProtocol=TCompactProtocol,
                                          TMemoryBuffer=TMemoryBuffer)
    previous = json.loads((ROOT / "scripts/parquet-date-from-csv-oracle/fixtures.json").read_text())
    pin = {key: previous[key] for key in
           ("cpython", "pyarrow", "pyarrow_wheel_sha256", "thrift", "thrift_wheel_sha256", "lean_toolchain")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == pin["pyarrow"]
    assert version("thrift") == pin["thrift"]
    assert (ROOT / "lean-toolchain").read_text().strip() == pin["lean_toolchain"]

    fingerprint = csv_tools["fingerprint"]
    lean_file = native["lean_bytes"]
    schema = pa.schema([pa.field(LABEL, pa.date32(), nullable=True)])
    pin["cases"] = {}
    pin["controls"] = {}
    with tempfile.TemporaryDirectory(prefix="parquet-date-csv-roundtrip-") as temporary:
        folder = Path(temporary)
        commands = []
        sources = {}
        outputs = {}
        native_inputs = {}
        setup = [generator["HARNESS"]]
        for case in NATIVE_EMPTY_CASES:
            _, wire = ipc["reference"](pa, LABEL, True, CASES[case])
            path = folder / f"{case}-input.parquet"
            setup.append(f"#eval emit {json.dumps(str(path))} {generator['bytes_term'](wire)}")
            native_inputs[case] = (path, fingerprint(wire))
        command = [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                   "-DwarningAsError=true"]
        producer = folder / "Producer.lean"
        producer.write_text("\n".join(setup) + "\n", encoding="utf-8")
        subprocess.run(command + [str(producer)], cwd=ROOT, check=True)
        for case, groups in CASES.items():
            path = folder / case
            path.mkdir()
            if case in native_inputs:
                path_in, ipc_pin = native_inputs[case]
                wire = path_in.read_bytes()
                producer_pin = {"pyarrow_ipc": ipc_pin, "lean_source_parquet": fingerprint(wire)}
            else:
                wire = source_file(pa, pq, schema, groups)
                producer_pin = {"pyarrow_parquet": fingerprint(wire)}
            opened = pq.ParquetFile(pa.BufferReader(wire))
            assert opened.schema_arrow == schema
            assert opened.num_row_groups == len(groups)
            for index, group in enumerate(groups):
                project = opened.read_row_group(index)
                assert project.num_rows == len(group)
                assert project.column(0).combine_chunks().view(pa.int32()).to_pylist() == group
            slots = [slot for group in groups for slot in group]
            text = pc.strftime(pa.array(slots, type=pa.int32()).view(pa.date32()), "%Y-%m-%d").to_pylist()
            rows = [[LABEL]] + [["N" if day is None else "T" + day] for day in text]
            sources[case] = wire
            outputs[case] = (path, slots, rows)
            commands.append(f"#eval cycle {json.dumps(str(path))} {lean_file(wire)}")
            pin["cases"][case] = {"source_groups": groups, **producer_pin}

        original = sources["cuts_a"]
        outside = source_file(pa, pq, schema, [[-1], [2932897]])
        late, offset = native["damage_second_group"](
            native["producer"](native["EDGE_DAYS"], pa.date32(), True, group_size=4))
        late_error = "(.toCsv (.source (.groupFailure 1 (.scan .unsupportedPageEncoding))))"
        pyarrow_empty = source_file(pa, pq, schema, CASES["mixed_empty"])
        opens = pq.ParquetFile(pa.BufferReader(pyarrow_empty))
        empty_chunk = opens.metadata.row_group(0).column(0)
        assert empty_chunk.num_values == empty_chunk.data_page_offset == 0
        empty_error = "(.toCsv (.source (.openFailure (.snapshot (.invalidMetadata .pageInterval)))))"
        controls = {
            "pyarrow_empty_page_interval": (pyarrow_empty, empty_error, ""),
            "export_total_rows": (original, "(.toCsv (.encode (.csvRowLimit 5 4)))",
                                  "{ limits with exportCsv := ⟨4096, 4⟩ }"),
            "import_total_rows": (original, "(.fromCsv (.csvToIpc (.csvRowLimit 5 4)))",
                                  "{ limits with importCsv := ⟨1024, 4⟩ }"),
            "late_outside_calendar": (outside, "(.toCsv (.encode (.csv (.csv (.printCell 0)))))", ""),
            "second_group_thrift_edit": (late, late_error, 'limits "date"'),
        }
        for case, (wire, error, settings) in controls.items():
            commands.append(f"#guard rejects {lean_file(wire)} {error} {settings}".rstrip())
            pin["controls"][case] = {"parquet": fingerprint(wire), "error": error}
        pin["controls"]["second_group_thrift_edit"]["modified_offset"] = offset
        harness = folder / "Oracle.lean"
        harness.write_text(TESTS.read_text(encoding="utf-8") + "\n" + "\n".join(commands) + "\n",
                           encoding="utf-8")
        subprocess.run(command + [str(harness)], cwd=ROOT, check=True)

        exports = {}
        for case, (path, slots, rows) in outputs.items():
            actual_csv = (path / "export.csv").read_bytes()
            assert actual_csv == csv_tools["csv_bytes"](rows, csv.QUOTE_ALL)
            with io.StringIO(actual_csv.decode("utf-8"), newline="") as stream:
                assert list(csv.reader(stream, strict=True)) == rows
            exports[case] = actual_csv
            normalized = (path / "normalized.parquet").read_bytes()
            leaf, body = emitted["observe_file"](pa, pq, normalized, schema, slots, native["raw_leaf"],
                                                  pages["header_fields"], TCompactProtocol, TMemoryBuffer)
            pin["cases"][case].update(canonical_csv=fingerprint(actual_csv), lean_parquet=fingerprint(normalized),
                                      v1_body=fingerprint(body), parquet_leaf=leaf)
        assert sources["cuts_a"] != sources["cuts_b"]
        assert exports["cuts_a"] == exports["cuts_b"] == exports["mixed_empty"]
        assert exports["cuts_a"] != exports["moved_null"]
        assert exports["cuts_a"] != exports["reordered_days"]
        assert exports["zero_groups"] == exports["empty_groups"]

    manifest = HERE / "fixtures.json"
    if args.regenerate:
        manifest.write_text(json.dumps(pin, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    else:
        assert pin == json.loads(manifest.read_text(encoding="utf-8")), json.dumps(pin, indent=2)
    print(f"PASS {len(CASES)} native DATE → CSV → DATE readbacks and {len(controls)} pinned controls")


if __name__ == "__main__":
    main()
