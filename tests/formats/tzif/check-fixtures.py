"""Check pinned IANA zoneinfo bytes with struct and CPython zoneinfo."""

from datetime import datetime, timedelta, timezone
import hashlib
from io import BytesIO
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
from zipfile import ZipFile
from zoneinfo import ZoneInfo


WHEEL_SHA256 = "1a403fada01ff9221ca8044d701868fa132215d84beb92242d9acd2147f667a8"
FIXTURES = {
    "Europe/Paris": "cd588e779c5737d70e4e47158dafab7945b026b2bb34454cc47741815459b068",
    "Asia/Gaza": "f8f0bffe018e0da0c682fe4b2f31fba6d34b6cd752b4f931198e0b99e6ef70d5",
    "Etc/UTC": "fddce1e648a1732ac29afd9a16151b2973cdf082e7ec0c690f7e42be6b598b93",
}
EPOCH = datetime(1970, 1, 1, tzinfo=timezone.utc)
NS = 1_000_000_000


def sections(data):
    ut, std, leap, time, types, chars = struct.unpack_from(">6I", data, 20)
    second = 44 + 5 * time + 6 * types + chars + 8 * leap + std + ut
    ut, std, leap, time, types, chars = struct.unpack_from(">6I", data, second + 20)
    start = second + 44
    end = start + 9 * time + 6 * types + chars + 12 * leap + std + ut
    assert leap == 0
    seconds = struct.unpack_from(f">{time}q", data, start)
    index_start = start + 8 * time
    type_start = index_start + time
    indices = data[index_start:type_start]
    designations = data[type_start + 6 * types:type_start + 6 * types + chars]
    local_types = []
    for i in range(types):
        offset, dst, designation = struct.unpack_from(">iBB", data, type_start + 6 * i)
        local_types.append((offset, bool(dst), designations[designation:].split(b"\0", 1)[0]))
    assert data[end] == data[-1] == 10
    return second, start, index_start, type_start, end, list(zip(seconds, indices, strict=True)), local_types


def tick_nanos(delta):
    return (delta.days * 86400 + delta.seconds) * NS + delta.microseconds * 1000


def local_nanos(zone, nanos):
    micros, remainder = divmod(nanos, 1000)
    instant = EPOCH + timedelta(microseconds=micros)
    local = instant.astimezone(zone).replace(tzinfo=timezone.utc)
    return tick_nanos(local - EPOCH) + remainder


def add_fixture(lines, name, data, directory):
    zone = ZoneInfo.from_file(BytesIO(data), key=name)
    second, start, _, _, end, rows, types = sections(data)
    path = directory / name.replace("/", "-")
    path.write_bytes(data)
    label = "check" + path.name.replace("-", "")
    lines.extend([
        f"private def {label} : IO Unit := do",
        f"  let file : Bytes := ⟨← IO.FS.readBinFile {json.dumps(str(path))}⟩",
        f"  let block ← require (parse file.length file) {json.dumps(name)}",
        f"  check (block.layout.version == .v{chr(data[4])}) \"version\"",
        f"  check (block.layout.secondHeader == {second} && block.layout.blockStart == {start} && "
        f"block.layout.blockEnd == {end}) \"layout\"",
        f"  check (block.footer == {list(data[end + 1:-1])}) \"opaque footer\"",
    ])
    lean_rows = ", ".join(f"({second}, {index})" for second, index in rows)
    lines.append("  check (block.transitions.map (fun row => (row.second, row.index.val)) == "
                 f"[{lean_rows}]) \"64-bit transition sequence and indices\"")
    lean_types = ", ".join(f"({off}, {str(dst).lower()}, {list(designation)})"
                           for off, dst, designation in types)
    lines.append("  check (block.types.toList.map (fun ty => (ty.offsetSeconds, ty.isDst, ty.designation)) "
                 f"== [{lean_types}]) \"offsets, DST flags and designations\"")
    if not rows:
        lines.append("  check ((block.toSchedule? ⟨0⟩ ⟨1⟩).isNone) \"opaque footer-only zone\"")
    else:
        instants = [second for second, _ in rows]
        cut_index = 0 if name == "Europe/Paris" else next(i for i, t in enumerate(instants) if t > 2**31 - 1)
        cut = instants[cut_index]
        lower, upper = cut - 3600, cut + 3600
        assert upper < instants[cut_index + 1]
        if name == "Europe/Paris":
            assert cut < -(2**31) and types[0][0] % 60
        lines.extend([
            f"  let schedule ← requireSome (block.toSchedule? ⟨{lower}⟩ ⟨{upper}⟩) \"schedule\"",
            f"  let startsAtCut ← requireSome (block.toSchedule? ⟨{cut}⟩ ⟨{upper}⟩) \"at cut\"",
            "  check (startsAtCut.transitions.isEmpty) \"cut at left endpoint becomes initial type\"",
            f"  check (startsAtCut.initial.nanoseconds == {local_nanos(zone, cut * NS) - cut * NS}) "
            "\"offset at cut\"",
            f"  check ((block.toSchedule? ⟨{cut}⟩ ⟨{instants[-1]}⟩).isSome) \"last boundary is exclusive\"",
            f"  check ((block.toSchedule? ⟨{cut}⟩ ⟨{instants[-1] + 1}⟩).isNone) \"tail unavailable\"",
            f"  check ((block.toSchedule? ⟨{cut}⟩ ⟨{cut}⟩).isNone) \"empty interval\"",
        ])
        for seconds in (lower, cut, upper):
            for shift in (-1001, -1, 0, 1, 1001):
                instant = seconds * NS + shift
                if lower * NS <= instant < upper * NS:
                    expected = f"some ⟨{local_nanos(zone, instant)}⟩"
                else:
                    expected = "none"
                lines.append(f"  check ((Rules.scheduled schedule).toLocal? ⟨{instant}⟩ == {expected}) "
                             f"\"wall time at {instant}\"")
    return label


def replace(data, at, replacement):
    return data[:at] + replacement + data[at + len(replacement):]


def add_negative_checks(lines, data, directory):
    second, start, indices, types, end, _, _ = sections(data)
    cases = (
        ("first-header-truncated", data[:43], "truncated"),
        ("second-header-truncated", data[:second + 43], "truncated"),
        ("selected-block-truncated", data[:end - 1], "truncated"),
        ("compat-count-overflow", replace(data, 32, b"\xff" * 4), "truncated"),
        ("selected-count-overflow", replace(data, second + 32, b"\xff" * 4), "truncated"),
        ("first-version", replace(data, 4, b"4"), "version"),
        ("different-second-version", replace(data, second + 4, b"3"), "version"),
        ("bad-magic", replace(data, second, b"!"), "header"),
        ("leaps", replace(data, second + 28, struct.pack(">I", 1)), "leapSeconds"),
        ("type-count-zero", replace(data, second + 36, struct.pack(">I", 0)), "counts"),
        ("wrong-transition-index", replace(data, indices, b"\xff"), "transitionType"),
        ("duplicate-transition", replace(data, start + 8, data[start:start + 8]), "transitionOrder"),
        ("wrong-designation-index", replace(data, types + 5, b"\xff"), "designation"),
        ("wrong-dst-flag", replace(data, types + 4, b"\x02"), "indicator"),
        ("invalid-offset", replace(data, types, struct.pack(">i", -(2**31))), "offset"),
        ("bad-footer-delimiter", replace(data, end, b"!"), "footer"),
        ("footer-extra-line", data + b"\n", "footer"),
    )
    lines.append("private def checkNegative : IO Unit := do")
    for name, payload, error in cases:
        path = directory / name
        path.write_bytes(payload)
        lines.append(f"  expectError {json.dumps(str(path))} .{error}")
    return len(cases)


def add_empty_footer(lines):
    lines.extend([
        "private def checkEmptyFooter : IO Unit := do",
        "  let header : List UInt8 := [84, 90, 105, 102, 50] ++ List.replicate 34 0 ++ [1, 0, 0, 0, 1]",
        "  let compatibility := header ++ [0, 0, 0, 0, 0, 0, 0]",
        "  let file := Bytes.ofList (compatibility ++ header ++ [0, 0, 0, 37, 0, 0, 0, 10, 10])",
        "  let block ← require (parse file.length file) \"empty footer\"",
        "  let schedule ← requireSome (block.toSchedule? ⟨-1⟩ ⟨1⟩) \"constant type zero\"",
        "  check (schedule.initial.nanoseconds == 37000000000) \"constant offset\"",
        "  match parse (file.length - 1) file with",
        "  | .error .sizeLimit => pure ()",
        "  | _ => throw (IO.userError \"file budget\")",
        "  let header := header.dropLast ++ [4]",
        "  let file := Bytes.ofList (compatibility ++ header ++ [0, 0, 0, 0, 0, 0, 45, 48, 48, 0, 10, 10])",
        "  let block ← require (parse file.length file) \"unspecified type\"",
        "  check ((block.toSchedule? ⟨-1⟩ ⟨1⟩).isNone) \"-00 has no offset semantics\"",
    ])


def main():
    assert sys.version_info[:3] == (3, 13, 5), sys.version
    wheel = Path(sys.argv[1]).read_bytes()
    assert hashlib.sha256(wheel).hexdigest() == WHEEL_SHA256
    root = Path(__file__).resolve().parents[3]
    lines = [
        "module",
        "import Silmaril.Formats.TZif.Defs",
        "meta import Silmaril.Formats.TZif.Defs",
        "meta import Silmaril.Formats.Bytes",
        "meta import Silmaril.Numeric.TimeZone.Defs",
        "meta import Silmaril.Numeric.Timestamp.Defs",
        "open Silmaril.Formats Silmaril.Formats.TZif Silmaril.Numeric.TimeZone",
        "private def check (ok : Bool) (label : String) : IO Unit :=",
        "  unless ok do throw (IO.userError label)",
        "private def require (result : Except Error Block) (label : String) : IO Block :=",
        "  match result with",
        "  | .ok block => pure block",
        "  | .error error => throw (IO.userError s!\"{label}: {repr error}\")",
        "private def requireSome (result : Option Schedule) (label : String) : IO Schedule :=",
        "  match result with",
        "  | some schedule => pure schedule",
        "  | none => throw (IO.userError label)",
        "private def expectError (path : System.FilePath) (expected : Error) : IO Unit := do",
        "  let file : Bytes := ⟨← IO.FS.readBinFile path⟩",
        "  match parse file.length file with",
        "  | .error error => check (error == expected) s!\"{path}: {repr error}\"",
        "  | .ok _ => throw (IO.userError s!\"{path}: unexpectedly accepted\")",
    ]
    with tempfile.TemporaryDirectory() as temporary, ZipFile(BytesIO(wheel)) as archive:
        directory = Path(temporary)
        assert archive.read("tzdata/zoneinfo/tzdata.zi").splitlines()[0] == b"# version 2025b"
        labels = []
        for name, digest in FIXTURES.items():
            data = archive.read("tzdata/zoneinfo/" + name)
            assert hashlib.sha256(data).hexdigest() == digest
            labels.append(add_fixture(lines, name, data, directory))
        negatives = add_negative_checks(lines, archive.read("tzdata/zoneinfo/Europe/Paris"), directory)
        add_empty_footer(lines)
        lean = directory / "Oracle.lean"
        lean.write_text("\n".join(lines + [f"#eval {name}" for name in
                                          (*labels, "checkNegative", "checkEmptyFooter")]) + "\n")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(lean)], cwd=root, check=True)
    print(f"IANA 2025b: {len(FIXTURES)} pinned TZif files, {negatives} malformed variants, "
          "and synthetic empty-footer cases passed")


if __name__ == "__main__":
    main()
