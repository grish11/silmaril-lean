"""Check pinned CSV fixtures in both directions with CPython's csv module."""

import csv
import hashlib
import io
import json
import os
from pathlib import Path
import platform
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[3]
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

meta import Silmaril.Formats.Csv.Defs

open Silmaril.Formats.Csv

private meta def check (source target : System.FilePath) (expected : Rows) : IO Unit := do
  let input ← IO.FS.readBinFile source
  unless decode input.data.toList == some expected do
    throw (IO.userError s!"CSV decode mismatch for {source}")
  let some output := encode expected
    | throw (IO.userError s!"CSV encode rejected {source}")
  IO.FS.writeBinFile target ⟨output.toArray⟩
"""


def digest(wire):
    return hashlib.sha256(wire).hexdigest()


def oracle_read(wire):
    stream = io.StringIO(wire.decode("ascii"), newline="")
    return list(csv.reader(stream, **DIALECT))


def oracle_write(rows):
    stream = io.StringIO(newline="")
    writer = csv.writer(stream, **DIALECT, lineterminator="\r\n", quoting=csv.QUOTE_ALL)
    writer.writerows(rows)
    return stream.getvalue().encode("ascii")


def lean_rows(rows):
    return json.dumps([[list(field.encode("ascii")) for field in row] for row in rows])


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def main():
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    oracle = manifest["oracle"]
    require(
        platform.python_implementation() == oracle["implementation"]
        and platform.python_version() == oracle["version"],
        f"Use {oracle['implementation']} {oracle['version']} for the pinned oracle.",
    )

    with tempfile.TemporaryDirectory(prefix="silmaril-csv-") as scratch:
        folder = Path(scratch)
        commands = [LEAN_DRIVER]
        for fixture in manifest["fixtures"]:
            name = fixture["name"]
            rows = fixture["rows"]
            wire = bytes.fromhex(fixture["wire_hex"])
            canonical = oracle_write(rows)
            require(digest(wire) == fixture["wire_sha256"], f"{name}: input hash mismatch")
            require(oracle_read(wire) == rows, f"{name}: oracle input rows differ")
            require(digest(canonical) == fixture["writer_sha256"], f"{name}: writer hash mismatch")
            if fixture["source"] == "cpython-writer":
                require(wire == canonical, f"{name}: input differs from pinned oracle writer")
            source = folder / f"{name}.csv"
            target = folder / f"{name}.out.csv"
            source.write_bytes(wire)
            commands.append(f'#eval check {json.dumps(str(source))} {json.dumps(str(target))} {lean_rows(rows)}')

        driver = folder / "Fixtures.lean"
        driver.write_text("\n".join(commands) + "\n", encoding="utf-8")
        subprocess.run(
            [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", driver],
            cwd=ROOT,
            check=True,
        )
        for fixture in manifest["fixtures"]:
            name = fixture["name"]
            output = (folder / f"{name}.out.csv").read_bytes()
            require(output == oracle_write(fixture["rows"]), f"{name}: Lean and oracle writer bytes differ")
            require(oracle_read(output) == fixture["rows"], f"{name}: oracle rejected Lean writer observation")
            print(f"PASS {name} {fixture['wire_sha256']}")


if __name__ == "__main__":
    main()
