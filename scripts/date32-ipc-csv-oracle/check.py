"""Pin both typed calendar CSV and single-batch Date32 IPC round trips."""

import argparse
import csv
from datetime import date
import io
import json
import os
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
TESTS = ROOT / "Silmaril/Formats/Arrow/DateStream/ToCsv/Tests.lean"
LABEL = "日付"


def ipc_term(wire):
    return f"(KBytes.leaf {len(wire)} 0x{int.from_bytes(wire, 'little'):x})"


def lean_string(value):
    return json.dumps(str(value), ensure_ascii=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pyarrow-path", type=Path)
    parser.add_argument("--regenerate", action="store_true", help="Update the fixture fingerprints")
    args = parser.parse_args()
    if args.pyarrow_path is not None:
        sys.path.insert(0, str(args.pyarrow_path.resolve()))
    import pyarrow as pa
    import pyarrow.compute as pc

    csv_oracle = ROOT / "scripts/date32-from-csv-oracle"
    csv_helpers = runpy.run_path(str(csv_oracle / "check.py"))
    ipc_helpers = runpy.run_path(str(ROOT / "scripts/arrow-date32-writer-oracle/check.py"))
    reference = ipc_helpers["reference"]
    observe = ipc_helpers["observe"]
    csv_bytes = csv_helpers["csv_bytes"]
    lean_bytes = csv_helpers["lean_bytes"]
    fingerprint = csv_helpers["fingerprint"]
    prior = json.loads((csv_oracle / "fixtures.json").read_text(encoding="utf-8"))
    pin = {key: prior[key] for key in ("cpython", "pyarrow", "pyarrow_wheel_sha256", "lean_toolchain")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == pin["pyarrow"]
    assert (ROOT / "lean-toolchain").read_text().strip() == pin["lean_toolchain"]

    endpoints = [-719528, -1, None, 0, 11016, 2932896]
    spellings = pc.strftime(pa.array(endpoints, type=pa.int32()).view(pa.date32()),
                            format="%Y-%m-%d").to_pylist()
    assert spellings == ["0000-01-01", "1969-12-31", None, "1970-01-01", "2000-02-29", "9999-12-31"]
    for day, text in zip(endpoints, spellings, strict=True):
        if text is not None and not text.startswith("0000"):
            assert (date.fromisoformat(text) - date(1970, 1, 1)).days == day
    cases = {
        "nullable_endpoints": (LABEL, True, endpoints, spellings),
        "required_empty_batch": ("date, jour", False, [], []),
    }
    pin["cases"] = {}
    pin["refusals"] = {}
    with tempfile.TemporaryDirectory(prefix="date32-ipc-csv-") as temporary:
        folder = Path(temporary)
        commands = []
        observations = {}
        for case, (name, nullable, slots, texts) in cases.items():
            path = folder / case
            path.mkdir()
            schema, source = reference(pa, name, nullable, [slots])
            observe(pa, source, schema, [slots])
            rows = [[name]] + [["N" if text is None else "T" + text] for text in texts]
            minimal, canonical = csv_bytes(rows), csv_bytes(rows, csv.QUOTE_ALL)
            if case == "nullable_endpoints":
                assert minimal != canonical
            commands.append(f"#eval cycles {lean_string(path)} {lean_string(name)} "
                            f"{str(nullable).lower()} {ipc_term(source)} {lean_bytes(minimal)} "
                            f"{lean_bytes(canonical)}")
            observations[case] = (path, schema, slots, rows, canonical)
            pin["cases"][case] = {
                "name": name, "nullable": nullable, "signed_slots": slots,
                "pyarrow_ipc": fingerprint(source), "cpython_csv_minimal": fingerprint(minimal),
                "cpython_csv_canonical": fingerprint(canonical),
            }

        _, mismatched = reference(pa, LABEL, False, [[-1]])
        _, date32 = reference(pa, LABEL, True, [[-1]])
        # Arrow can carry both adjacent days as Date32 even though the CSV profile cannot.
        outside = [-719529, 2932897]
        assert pc.strftime(pa.array(outside, type=pa.int32()).view(pa.date32()),
                           format="%Y-%m-%d").to_pylist() == ["-0001-12-31", "10000-01-01"]
        narrow_helpers = runpy.run_path(str(ROOT / "scripts/arrow-date64-narrow-oracle/check.py"))
        date64 = narrow_helpers["ipc_stream"](pa, pa.date64(), pa.int64(), [[-86400000]])
        refusals = {
            "below_profile": (reference(pa, LABEL, True, [[outside[0]]])[1], "(.csv (.csv (.printCell 0)))", ""),
            "above_profile": (reference(pa, LABEL, True, [[outside[1]]])[1], "(.csv (.csv (.printCell 0)))", ""),
            "schema_only": (reference(pa, LABEL, True, [])[1], "(.batchCount 0)", ""),
            "two_batches": (reference(pa, LABEL, True, [[], [-1]])[1], "(.batchCount 2)", ""),
            "date64": (date64, "(.descriptor ⟨\"日付\", true, .millisecond⟩)", ""),
            "wrong_nullability": (mismatched, "(.descriptor ⟨\"日付\", false, .day⟩)", ""),
            "wrong_name": (date32, "(.descriptor ⟨\"日付\", true, .day⟩)", ' "other"'),
        }
        for case, (wire, error, declaration) in refusals.items():
            commands.append(f"#guard rejects {ipc_term(wire)} {error}{declaration}")
            pin["refusals"][case] = fingerprint(wire)

        driver = folder / "Oracle.lean"
        driver.write_text(TESTS.read_text(encoding="utf-8") + "\n" + "\n".join(commands) + "\n",
                          encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(driver)], cwd=ROOT, check=True)
        for case, (path, schema, slots, rows, canonical) in observations.items():
            for leaf in ("from-ipc.csv", "csv-cycle.csv"):
                actual = (path / leaf).read_bytes()
                assert actual == canonical
                with io.StringIO(actual.decode("utf-8"), newline="") as stream:
                    assert list(csv.reader(stream, strict=True)) == rows
                pin["cases"][case][leaf] = fingerprint(actual)
            for leaf in ("from-csv.arrow", "ipc-cycle.arrow"):
                actual = (path / leaf).read_bytes()
                observe(pa, actual, schema, [slots])
                pin["cases"][case][leaf] = fingerprint(actual)

    manifest = HERE / "fixtures.json"
    if args.regenerate:
        manifest.write_text(json.dumps(pin, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    else:
        assert pin == json.loads(manifest.read_text(encoding="utf-8")), json.dumps(pin, indent=2)
    print(f"PASS {len(cases)} pinned bidirectional CSV/IPC cases and {len(refusals)} IPC refusals")


if __name__ == "__main__":
    main()
