"""Check the UTF-8 CSV wire profile against pinned CPython fixtures."""

import csv
import hashlib
import io
import json
import os
from pathlib import Path
import platform
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
MANIFEST = Path(__file__).with_name("fixtures.json")
DIALECT = {
    "delimiter": ",",
    "quotechar": '"',
    "doublequote": True,
    "escapechar": None,
    "skipinitialspace": False,
    "strict": True,
}
LEAN_DRIVER = """\
module

meta import Silmaril.Formats.Csv.Utf8.Defs

open Silmaril.Formats.Csv (Rows)
open Silmaril.Formats.Csv.Utf8 (decode encode)

private meta def check (source target : System.FilePath) (expected : Rows) : IO Unit := do
  let input ← IO.FS.readBinFile source
  unless decode input.data.toList == some expected do
    throw (IO.userError s!"UTF-8 CSV decode mismatch for {source}")
  let some output := encode expected
    | throw (IO.userError s!"UTF-8 CSV encode rejected {source}")
  IO.FS.writeBinFile target ⟨output.toArray⟩

private meta def reject (source : System.FilePath) : IO Unit := do
  let input ← IO.FS.readBinFile source
  unless decode input.data.toList == none do
    throw (IO.userError s!"UTF-8 CSV accepted malformed bytes in {source}")
"""


def oracle_read(wire):
    stream = io.StringIO(wire.decode("utf-8", errors="strict"), newline="")
    return list(csv.reader(stream, **DIALECT))


def oracle_write(rows):
    stream = io.StringIO(newline="")
    writer = csv.writer(stream, **DIALECT, lineterminator="\r\n", quoting=csv.QUOTE_ALL)
    writer.writerows(rows)
    return stream.getvalue().encode("utf-8", errors="strict")


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def check_hash(wire, expected, name):
    require(hashlib.sha256(wire).hexdigest() == expected, f"{name}: hash mismatch")


def require_invalid_utf8(wire, name):
    try:
        wire.decode("utf-8", errors="strict")
    except UnicodeDecodeError:
        return
    raise SystemExit(f"{name}: CPython accepted malformed UTF-8 fixture")


def lean_rows(rows):
    return json.dumps([[list(field.encode("utf-8")) for field in row] for row in rows])


def main():
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    oracle = manifest["oracle"]
    require(
        platform.python_implementation() == oracle["implementation"]
        and platform.python_version() == oracle["version"],
        f"Use {oracle['implementation']} {oracle['version']} for the pinned oracle.",
    )
    with tempfile.TemporaryDirectory(prefix="silmaril-csv-utf8-") as scratch:
        folder = Path(scratch)
        commands = [LEAN_DRIVER]
        for fixture in manifest["fixtures"] + manifest["malformed_utf8"]:
            name = fixture["name"]
            wire = bytes.fromhex(fixture["wire_hex"])
            check_hash(wire, fixture["wire_sha256"], name)
            source = folder / f"{name}.csv"
            source.write_bytes(wire)
            source_term = json.dumps(str(source))
            if "rows" in fixture:
                rows = fixture["rows"]
                require(oracle_read(wire) == rows, f"{name}: CPython input rows differ")
                canonical = oracle_write(rows)
                check_hash(canonical, fixture["writer_sha256"], f"{name} writer")
                if fixture["source"] == "cpython-writer":
                    require(canonical == wire, f"{name}: input differs from CPython writer")
                target = json.dumps(str(folder / f"{name}.lean.csv"))
                commands.append(f"#eval check {source_term} {target} {lean_rows(rows)}")
            else:
                require_invalid_utf8(wire, name)
                commands.append(f"#eval reject {source_term}")

        driver = folder / "Fixtures.lean"
        driver.write_text("\n".join(commands) + "\n", encoding="utf-8")
        subprocess.run(
            [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", driver],
            cwd=ROOT,
            check=True,
        )
        for fixture in manifest["fixtures"]:
            name = fixture["name"]
            output = (folder / f"{name}.lean.csv").read_bytes()
            rows = fixture["rows"]
            require(output == oracle_write(rows), f"{name}: Lean and CPython writer bytes differ")
            require(oracle_read(output) == rows, f"{name}: CPython read of Lean output differs")
            print(f"PASS {name} {fixture['wire_sha256']}")
        for fixture in manifest["malformed_utf8"]:
            print(f"PASS {fixture['name']} rejected {fixture['wire_sha256']}")


if __name__ == "__main__":
    main()
