"""Check typed UTF-8 CSV wire observations with a pinned CPython CSV oracle."""

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
HEADER = ["名前", "i32"]
DIALECT = {
    "delimiter": ",",
    "quotechar": '"',
    "doublequote": True,
    "escapechar": None,
    "skipinitialspace": False,
    "strict": True,
}
LEAN_DRIVER = r"""
module

meta import Silmaril.Formats.Csv.Typed.Utf8.Defs
meta import Silmaril.Formats.Csv.Typed.Codecs.Defs

open Silmaril.Formats.Csv.Typed (CellCodec Error Schema Table)
open Silmaril.Formats.Csv.Typed.Utf8 (decode encode string)

private inductive Kind where
  | text
  | int32

private meta def Value : Kind → Type
  | .text => String
  | .int32 => Int32

private meta def schema : Schema Kind :=
  ⟨2, Fin.cases ("名前".toUTF8.data.toList, .text)
    (fun _ => ("i32".toUTF8.data.toList, .int32))⟩

private meta def codecs : (k : Kind) → CellCodec (Value k)
  | .text => string
  | .int32 => Silmaril.Formats.Csv.Typed.Codecs.int32

private meta def check (source target : System.FilePath) (expected : List (Option String × Option Int32)) :
    IO Unit := do
  let bytes ← IO.FS.readBinFile source
  let actual := (decode schema codecs bytes.data.toList).map fun table =>
    table.map fun row => (row (0 : Fin 2), row (1 : Fin 2))
  unless actual == .ok expected do
    throw (IO.userError s!"typed decode mismatch for {source}")
  let table : Table schema Value := expected.map fun (text, number) =>
    Fin.cases text (fun _ => number)
  let .ok output := encode schema codecs table
    | throw (IO.userError s!"typed encode rejected {source}")
  IO.FS.writeBinFile target ⟨output.toArray⟩

private meta def reject (source : System.FilePath) (error : Error) : IO Unit := do
  let bytes ← IO.FS.readBinFile source
  unless (decode schema codecs bytes.data.toList).map List.length == .error error do
    throw (IO.userError s!"wrong rejection for {source}")
"""


def oracle_read(wire):
    return list(csv.reader(io.StringIO(wire.decode("utf-8"), newline=""), **DIALECT))


def oracle_write(rows):
    stream = io.StringIO(newline="")
    csv.writer(stream, **DIALECT, lineterminator="\r\n", quoting=csv.QUOTE_ALL).writerows(rows)
    return stream.getvalue().encode("utf-8")


def lexical(values):
    return [HEADER] + [["N" if cell is None else f"T{cell}" for cell in row] for row in values]


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def check_hash(wire, expected, name):
    require(hashlib.sha256(wire).hexdigest() == expected, f"{name}: hash mismatch")


def check_host_negative(wire, fixture):
    name = fixture["name"]
    if "rows" in fixture:
        require(oracle_read(wire) == fixture["rows"], f"{name}: wrong CPython lexical rows")
        return
    expected = {"utf8": UnicodeDecodeError, "csv": csv.Error}[fixture["host_error"]]
    try:
        oracle_read(wire)
    except expected:
        return
    raise SystemExit(f"{name}: expected CPython {expected.__name__}")


def lean_expected(values):
    def string_option(value):
        return "none" if value is None else "(some " + json.dumps(value, ensure_ascii=False) + ")"

    def int32_option(value):
        return "none" if value is None else f"(some ({value} : Int32))"

    return "[" + ", ".join(
        f"({string_option(text)}, {int32_option(number)})" for text, number in values
    ) + "]"


def main():
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    oracle = manifest["oracle"]
    require(
        platform.python_implementation() == oracle["implementation"]
        and platform.python_version() == oracle["version"],
        f"Use {oracle['implementation']} {oracle['version']} for the pinned oracle.",
    )
    with tempfile.TemporaryDirectory(prefix="silmaril-typed-utf8-csv-") as scratch:
        folder = Path(scratch)
        commands = [LEAN_DRIVER]
        for fixture in manifest["accepted"]:
            name = fixture["name"]
            rows = lexical(fixture["values"])
            canonical = oracle_write(rows)
            check_hash(canonical, fixture["writer_sha256"], f"{name} writer")
            wire = bytes.fromhex(fixture["wire_hex"]) if "wire_hex" in fixture else canonical
            check_hash(wire, fixture["wire_sha256"], name)
            require(oracle_read(wire) == rows, f"{name}: CPython input rows differ")
            source = folder / f"{name}.csv"
            target = folder / f"{name}.lean.csv"
            source.write_bytes(wire)
            terms = lean_expected(fixture["values"])
            commands.append(f"#eval check {json.dumps(str(source))} {json.dumps(str(target))} {terms}")

        for fixture in manifest["rejected"]:
            name = fixture["name"]
            wire = bytes.fromhex(fixture["wire_hex"])
            check_hash(wire, fixture["wire_sha256"], name)
            check_host_negative(wire, fixture)
            source = folder / f"{name}.csv"
            source.write_bytes(wire)
            tag, *arguments = fixture["lean_error"]
            lean_error = " ".join([f".{tag}"] + [str(arg) for arg in arguments])
            commands.append(f"#eval reject {json.dumps(str(source))} ({lean_error})")

        driver = folder / "Fixtures.lean"
        driver.write_text("\n".join(commands) + "\n", encoding="utf-8")
        subprocess.run(
            [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", driver],
            cwd=ROOT,
            check=True,
        )
        for fixture in manifest["accepted"]:
            name = fixture["name"]
            output = (folder / f"{name}.lean.csv").read_bytes()
            rows = lexical(fixture["values"])
            require(output == oracle_write(rows), f"{name}: Lean and CPython writer bytes differ")
            require(oracle_read(output) == rows, f"{name}: CPython read of Lean output differs")
            print(f"PASS {name} {fixture['wire_sha256']}")
        for fixture in manifest["rejected"]:
            print(f"PASS {fixture['name']} rejected {fixture['wire_sha256']}")


if __name__ == "__main__":
    main()
