"""Check the concrete CSV cell codecs against the pinned host conversions."""

import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
MANIFEST = Path(__file__).with_name("fixtures.json")
DRIVER = """\
module

meta import Silmaril.Formats.Csv.Typed.Codecs.Defs

open Silmaril.Formats.Csv (Field)
open Silmaril.Formats.Csv.Typed (CellCodec)
open Silmaril.Formats.Csv.Typed.Codecs

private meta def check {α : Type} [BEq α] (codec : CellCodec α) (host : Field)
    (expected : α) (output : System.FilePath) : IO Unit := do
  unless codec.parse host == some expected do
    throw (IO.userError s!"Lean rejected the host value for {output}")
  let some field := codec.print expected
    | throw (IO.userError s!"Lean rejected the original value for {output}")
  IO.FS.writeBinFile output ⟨field.toArray⟩
"""


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def allowed_text(field):
    return all(byte in (10, 13) or 32 <= byte <= 126 for byte in field)


def host_print(kind, value):
    if kind == "int32":
        require(-(2**31) <= value < 2**31, "Fixture integer is outside Int32")
        return str(value).encode("ascii")
    require(kind == "utf8", f"Unknown fixture kind {kind}")
    field = value.encode("utf-8")
    require(allowed_text(field), "Fixture string is outside the CSV alphabet")
    return field


def host_parse(kind, field):
    if kind == "int32":
        require(re.fullmatch(rb"0|-?[1-9][0-9]*", field), f"Noncanonical decimal {field!r}")
        value = int(field, 10)
        require(-(2**31) <= value < 2**31, f"Out-of-range decimal {field!r}")
        return value
    require(allowed_text(field), f"Text is outside the CSV alphabet {field!r}")
    return field.decode("utf-8", errors="strict")


def main():
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    require(
        platform.python_implementation() == manifest["oracle"]
        and platform.python_version() == manifest["version"],
        f"Use {manifest['oracle']} {manifest['version']} for the pinned oracle.",
    )
    with tempfile.TemporaryDirectory(prefix="silmaril-csv-codecs-") as scratch:
        folder = Path(scratch)
        commands = [DRIVER]
        outputs = []
        for index, fixture in enumerate(manifest["fixtures"]):
            kind, value = fixture["kind"], fixture["value"]
            host = host_print(kind, value)
            require(hashlib.sha256(host).hexdigest() == fixture["field_sha256"], f"Vector {index} hash changed")
            target = folder / f"{index}.txt"
            expected = f"({value} : Int32)" if kind == "int32" else json.dumps(value)
            commands.append(f"#eval check {kind} {list(host)} {expected} {json.dumps(str(target))}")
            outputs.append((kind, value, host, target))

        driver = folder / "Host.lean"
        driver.write_text("\n".join(commands) + "\n", encoding="utf-8")
        subprocess.run(
            [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", driver],
            cwd=ROOT,
            check=True,
        )
        for kind, value, host, target in outputs:
            lean = target.read_bytes()
            require(host_parse(kind, lean) == value, f"Host rejected the Lean value for {target.name}")
            require(lean == host, f"Canonical bytes differ for {target.name}")
            print(f"PASS {kind} {value!r}")


if __name__ == "__main__":
    main()
