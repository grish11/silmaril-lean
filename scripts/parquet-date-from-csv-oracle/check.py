"""Produce typed calendar CSV with CPython and read Lean DATE files with PyArrow and Thrift."""

import argparse
import csv
from datetime import date
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
TESTS = ROOT / "Silmaril/Formats/Parquet/Date/FromCsv/Tests.lean"
LABEL = "日付"


def lean_string(value):
    return json.dumps(str(value), ensure_ascii=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pyarrow-path", type=Path)
    parser.add_argument("--thrift-path", type=Path)
    parser.add_argument("--regenerate", action="store_true", help="Update the fixture fingerprints")
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

    csv_oracle = runpy.run_path(str(ROOT / "scripts/date32-from-csv-oracle/check.py"))
    csv_bytes = csv_oracle["csv_bytes"]
    fingerprint = csv_oracle["fingerprint"]
    lean_bytes = csv_oracle["lean_bytes"]
    reader = runpy.run_path(str(ROOT / "scripts/arrow-date32-to-parquet-oracle/check.py"))
    footer = runpy.run_path(str(ROOT / "scripts/parquet-date-oracle/check.py"))
    raw_leaf = footer["raw_leaf"]
    raw_leaf.__globals__.update(TType=TType, TCompactProtocol=TCompactProtocol,
                                TMemoryBuffer=TMemoryBuffer)
    page = runpy.run_path(str(ROOT / "scripts/parquet-scalar-page/PyArrowOracle.py"))
    previous = json.loads(reader["MANIFEST"].read_text(encoding="utf-8"))
    pin = {key: previous[key] for key in
           ("cpython", "pyarrow", "pyarrow_wheel_sha256", "thrift", "thrift_wheel_sha256", "lean_toolchain")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == pin["pyarrow"]
    assert version("thrift") == pin["thrift"]
    assert (ROOT / "lean-toolchain").read_text().strip() == pin["lean_toolchain"]

    slots = [-719528, -719469, -25509, -1, None, 0, 11016, 2932896]
    spellings = pc.strftime(pa.array(slots, type=pa.int32()).view(pa.date32()), "%Y-%m-%d").to_pylist()
    assert spellings == ["0000-01-01", "0000-02-29", "1900-02-28", "1969-12-31", None,
                         "1970-01-01", "2000-02-29", "9999-12-31"]
    for day, spelling in zip(slots, spellings, strict=True):
        if spelling is not None and not spelling.startswith("0000"):
            assert (date.fromisoformat(spelling) - date(1970, 1, 1)).days == day

    rows = [[LABEL]] + [["N" if value is None else "T" + value] for value in spellings]
    required = "date, jour"
    cases = {
        "optional": (LABEL, True, slots, csv_bytes(rows)),
        "required": (required, False, [-1, 11016],
                     csv_bytes([[required], ["T1969-12-31"], ["T2000-02-29"]], csv.QUOTE_ALL)),
        "empty_optional": (LABEL, True, [], csv_bytes([[LABEL]])),
        "empty_required": (required, False, [], csv_bytes([[required]])),
    }
    adjacent = [-719529, 2932897]
    before, after = pc.strftime(pa.array(adjacent, type=pa.int32()).view(pa.date32()), "%Y-%m-%d").to_pylist()
    assert (before, after) == ("-0001-12-31", "10000-01-01")
    parse = "(.csv (.parseCell 0))"
    refusals = {
        "required_null": (csv_bytes([[LABEL], ["N"]]), False, "(.requiredNull 0 0)"),
        "bad_header": (csv_bytes([["other"], ["N"]]), True, "(.csv .headerMismatch)"),
        "bad_width": (csv_bytes([[LABEL], ["N", "N"]]), True, "(.csv (.width 1 2))"),
        "bad_leap_day": (csv_bytes([[LABEL], ["T1900-02-29"]]), True, parse),
        "before_range": (csv_bytes([[LABEL], ["T" + before]]), True, parse),
        "after_range": (csv_bytes([[LABEL], ["T" + after]]), True, parse),
        "unterminated": ((LABEL + '\r\n"T1970-01-01\r\n').encode("utf-8"), True, "(.csv .malformedWire)"),
    }
    pin["cases"] = {}
    pin["refusals"] = {}
    with tempfile.TemporaryDirectory(prefix="parquet-date-from-csv-") as temporary:
        folder = Path(temporary)
        commands = []
        for case, (name, nullable, expected, wire) in cases.items():
            path = lean_string(folder / (case + ".parquet"))
            commands.append(f"#eval emitFixture {path} {lean_string(name)} "
                            f"{str(nullable).lower()} {lean_bytes(wire)}")
            pin["cases"][case] = {"name": name, "nullable": nullable, "signed_slots": expected,
                                  "cpython_csv": fingerprint(wire)}
        for case, (wire, nullable, cause) in refusals.items():
            error = f"(.csvToIpc (.csv {cause}))"
            commands.append(f"#guard rejects {lean_bytes(wire)} {str(nullable).lower()} {error}")
            pin["refusals"][case] = {"csv": fingerprint(wire), "error": error}
        harness = folder / "Oracle.lean"
        harness.write_text(TESTS.read_text(encoding="utf-8") + "\n" + "\n".join(commands) + "\n",
                           encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(harness)], cwd=ROOT, check=True)
        for case, (name, nullable, expected, _) in cases.items():
            wire = (folder / (case + ".parquet")).read_bytes()
            schema = pa.schema([pa.field(name, pa.date32(), nullable=nullable)])
            leaf, body = reader["observe_file"](pa, pq, wire, schema, expected, raw_leaf,
                                                page["header_fields"], TCompactProtocol, TMemoryBuffer)
            pin["cases"][case].update(lean_parquet=fingerprint(wire), v1_body=fingerprint(body),
                                      parquet_leaf=leaf)

    manifest = HERE / "fixtures.json"
    if args.regenerate:
        manifest.write_text(json.dumps(pin, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    else:
        assert pin == json.loads(manifest.read_text(encoding="utf-8")), json.dumps(pin, indent=2)
    print(f"PASS {len(cases)} CSV-to-Parquet DATE cases and {len(refusals)} pinned CSV refusals")


if __name__ == "__main__":
    main()
