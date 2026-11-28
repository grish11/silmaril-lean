"""Pin PyArrow batch cuts and independently check canonical CSV and normalized IPC."""

import argparse
import csv
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
TESTS = ROOT / "Silmaril/Formats/Arrow/DateStream/ToCsv/RowObservational/Tests.lean"
LABEL = "日付"
CASES = {
    "cuts_a": [[-719528, None], [11016, 2932896]],
    "cuts_b": [[], [-719528], [], [], [None, 11016], [2932896], []],
    "null_moved": [[None, -719528], [11016, 2932896]],
    "days_reordered": [[2932896, None], [11016, -719528]],
    "schema_only": [],
    "consecutive_empties": [[], [], []],
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pyarrow-path", type=Path)
    parser.add_argument("--regenerate", action="store_true", help="Update the fixture fingerprints")
    args = parser.parse_args()
    if args.pyarrow_path is not None:
        sys.path.insert(0, str(args.pyarrow_path.resolve()))
    import pyarrow as pa
    import pyarrow.compute as pc

    prior = ROOT / "scripts/date32-ipc-csv-oracle"
    roundtrip = runpy.run_path(str(prior / "check.py"))
    writer = runpy.run_path(str(ROOT / "scripts/arrow-date32-writer-oracle/check.py"))
    csv_import = runpy.run_path(str(ROOT / "scripts/date32-from-csv-oracle/check.py"))
    old_pin = json.loads((prior / "fixtures.json").read_text(encoding="utf-8"))
    pin = {key: old_pin[key] for key in ("cpython", "pyarrow", "pyarrow_wheel_sha256", "lean_toolchain")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == pin["pyarrow"]
    assert (ROOT / "lean-toolchain").read_text().strip() == pin["lean_toolchain"]

    pin["cases"] = {}
    pin["refusals"] = {}
    ipc_term = roundtrip["ipc_term"]
    fingerprint = csv_import["fingerprint"]
    with tempfile.TemporaryDirectory(prefix="date32-row-observational-") as temporary:
        folder = Path(temporary)
        commands = []
        fixtures = {}
        for case, batches in CASES.items():
            path = folder / case
            path.mkdir()
            schema, source = writer["reference"](pa, LABEL, True, batches)
            writer["observe"](pa, source, schema, batches)
            slots = [day for batch in batches for day in batch]
            spellings = pc.strftime(pa.array(slots, type=pa.int32()).view(pa.date32()),
                                    format="%Y-%m-%d").to_pylist()
            rows = [[LABEL]] + [["N" if text is None else "T" + text] for text in spellings]
            expected = csv_import["csv_bytes"](rows, csv.QUOTE_ALL)
            fixtures[case] = (path, schema, source, slots, rows, expected)
            commands.append(f"#eval cycle {roundtrip['lean_string'](path)} {ipc_term(source)}")
            pin["cases"][case] = {"batches": batches, "pyarrow_source": fingerprint(source)}

        _, _, source, slots, _, expected = fixtures["cuts_a"]
        body_length = len(expected)
        ipc = ipc_term(source)
        _, outside = writer["reference"](pa, LABEL, True, [[-1], [2932897]])
        refusals = {
            "total_csv_rows": (source, f"{ipc} (.csvRowLimit {len(slots)} 2) ⟨1024, 2⟩ {{ rows := 2 }}"),
            "canonical_csv_bytes": (
                source, f"{ipc} (.csvByteLimit {body_length} {body_length - 1}) ⟨{body_length - 1}, 4⟩"
            ),
            "ipc_per_batch_rows": (
                source, f"{ipc} (.reader (.batch 0 (.metadata (.limit .rows)))) bounds {{ rows := 1 }}"
            ),
            "late_truncated_eos": (
                source[:-1], f"{ipc_term(source[:-1])} (.reader (.batch 2 (.envelope (.malformed .truncated))))"
            ),
            "late_outside_calendar": (outside, f"{ipc_term(outside)} (.csv (.csv (.printCell 0)))"),
        }
        for case, (wire, guard) in refusals.items():
            commands.append("#guard rejects " + guard)
            pin["refusals"][case] = fingerprint(wire)
        driver = folder / "Oracle.lean"
        driver.write_text(TESTS.read_text(encoding="utf-8") + "\n" + "\n".join(commands) + "\n",
                          encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(driver)], cwd=ROOT, check=True)

        exports = {}
        for case, (path, schema, _, slots, rows, expected) in fixtures.items():
            exported = (path / "export.csv").read_bytes()
            normalized = (path / "normalized.arrow").read_bytes()
            with io.StringIO(exported.decode("utf-8"), newline="") as stream:
                assert list(csv.reader(stream, strict=True)) == rows
            assert exported == expected
            writer["observe"](pa, normalized, schema, [slots])
            exports[case] = exported
            pin["cases"][case]["canonical_csv"] = fingerprint(exported)
            pin["cases"][case]["normalized_ipc"] = fingerprint(normalized)
        assert exports["cuts_a"] == exports["cuts_b"]
        assert exports["cuts_a"] != exports["null_moved"]
        assert exports["cuts_a"] != exports["days_reordered"]
        assert exports["schema_only"] == exports["consecutive_empties"]
        assert fixtures["cuts_a"][2] != fixtures["cuts_b"][2]

    manifest = HERE / "fixtures.json"
    if args.regenerate:
        manifest.write_text(json.dumps(pin, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    else:
        assert pin == json.loads(manifest.read_text(encoding="utf-8")), json.dumps(pin, indent=2)
    print(f"PASS {len(CASES)} PyArrow sources, exact canonical CSV and singleton readback, "
          f"and {len(refusals)} refusal controls")


if __name__ == "__main__":
    main()
