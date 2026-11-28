"""Compare supplied whole-second tables with pinned IANA-derived TZif bytes."""

from datetime import datetime, timedelta, timezone
import hashlib
from io import BytesIO
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from zipfile import ZipFile
from zoneinfo import ZoneInfo


WHEEL_SHA256 = "1a403fada01ff9221ca8044d701868fa132215d84beb92242d9acd2147f667a8"
EPOCH = datetime(1970, 1, 1, tzinfo=timezone.utc)
NS_PER_SECOND = 1_000_000_000
PROBES = (-1_000_000, -1000, -1, 0, 1, 1000, 1_000_000)
FIXTURES = (
    ("America/New_York", "2025-01-01", "2026-01-01",
     ("2025-03-09T07:00:00", "2025-11-02T06:00:00")),
    ("Asia/Kathmandu", "1985-12-31", "1986-01-02", ("1985-12-31T18:30:00",)),
    ("Europe/Paris", "1911-03-10", "1911-03-12", ("1911-03-10T23:50:39",)),
)


def nominal_nanos(time):
    delta = time.replace(tzinfo=timezone.utc) - EPOCH
    return (delta.days * 86400 + delta.seconds) * NS_PER_SECOND + delta.microseconds * 1000


def utc_second(text):
    return nominal_nanos(datetime.fromisoformat(text)) // NS_PER_SECOND


def split_nanos(nanos):
    micros, residual = divmod(nanos, 1000)
    return EPOCH + timedelta(microseconds=micros), residual


def offset_at(zone, second):
    offset = (EPOCH + timedelta(seconds=second)).astimezone(zone).utcoffset()
    assert offset.microseconds == 0
    return offset.days * 86400 + offset.seconds


def local_candidates(zone, nanos, start, stop):
    nominal, residual = split_nanos(nanos)
    wall = nominal.replace(tzinfo=None)
    candidates = set()
    for fold in (0, 1):
        utc = wall.replace(tzinfo=zone, fold=fold).astimezone(timezone.utc)
        if utc.astimezone(zone).replace(tzinfo=None) == wall:
            candidate = nominal_nanos(utc) + residual
            if start <= candidate < stop:
                candidates.add(candidate)
    return sorted(candidates)


def lean_ticks(kind, nanos):
    for unit, scale in (("second", NS_PER_SECOND), ("millisecond", 1_000_000),
                        ("microsecond", 1000), ("nanosecond", 1)):
        if nanos % scale == 0:
            return f"(⟨{nanos // scale}⟩ : Ticks .{kind} .{unit})"
    raise AssertionError("nanoseconds are always exact")


def add_fixture(checks, archive, index, name, start_text, stop_text, cut_texts):
    with BytesIO(archive.read("tzdata/zoneinfo/" + name)) as tzif:
        zone = ZoneInfo.from_file(tzif, key=name)
    start, stop = utc_second(start_text), utc_second(stop_text)
    cuts = [utc_second(text) for text in cut_texts]
    rows = [(cut, offset_at(zone, cut)) for cut in cuts]
    initial = offset_at(zone, start)
    for cut, after in rows:
        assert offset_at(zone, cut - 1) != after
    for (left, offset), right in zip([(start, initial)] + rows, cuts + [stop], strict=True):
        assert all(offset_at(zone, second) == offset for second in range(left, right, 3600))
        assert offset_at(zone, right - 1) == offset

    label = f"zone{index}"
    lean_rows = ", ".join(f"⟨⟨{cut}⟩, {after}⟩" for cut, after in rows)
    checks.append(f"private def {label} := NamedZone.ofTransitions? {json.dumps(name)} "
                  f"⟨{start}⟩ ⟨{stop}⟩ ({initial}) [{lean_rows}]")
    checks.append(f"#guard {label}.isSome")

    for second in (start, *cuts, stop):
        for shift in PROBES:
            nanos = second * NS_PER_SECOND + shift
            expected = "none"
            if start * NS_PER_SECOND <= nanos < stop * NS_PER_SECOND:
                utc, residual = split_nanos(nanos)
                wall = nominal_nanos(utc.astimezone(zone)) + residual
                expected = f"some ⟨{wall}⟩"
            checks.append(f"#guard ({label}.bind fun zone => zone.toLocal? "
                          f"{lean_ticks('utcInstant', nanos)}) = {expected}")

    wall_boundaries = {start + initial, stop + offset_at(zone, stop - 1)}
    for cut, after in rows:
        wall_boundaries.update((cut + offset_at(zone, cut - 1), cut + after))
    for second in sorted(wall_boundaries):
        for shift in PROBES:
            nanos = second * NS_PER_SECOND + shift
            candidates = local_candidates(zone, nanos, start * NS_PER_SECOND, stop * NS_PER_SECOND)
            if not candidates:
                expected = ".noSolution"
            elif len(candidates) == 1:
                expected = f"(.unique ⟨{candidates[0]}⟩)"
            else:
                first, second_candidate = candidates
                expected = f"(.ambiguous ⟨{first}⟩ ⟨{second_candidate}⟩ [])"
            checks.append(f"#guard ({label}.map fun zone => zone.resolveLocal "
                          f"{lean_ticks('localReading', nanos)}) = some {expected}")


def main():
    assert sys.version_info[:3] == (3, 13, 5), sys.version
    wheel = Path(sys.argv[1]).read_bytes()
    assert hashlib.sha256(wheel).hexdigest() == WHEEL_SHA256
    declarations = [
        "module",
        "import Silmaril.Numeric.TimeZone.Named.Defs",
        "meta import Silmaril.Numeric.TimeZone.Named.Defs",
        "meta import Silmaril.Numeric.TimeZone.Defs",
        "meta import Silmaril.Numeric.Timestamp.Defs",
        "open Silmaril.Numeric.TimeZone Silmaril.Numeric.Timestamp",
    ]
    checks = []
    with ZipFile(BytesIO(wheel)) as archive:
        assert archive.read("tzdata/zoneinfo/tzdata.zi").splitlines()[0] == b"# version 2025b"
        for index, fixture in enumerate(FIXTURES):
            add_fixture(checks, archive, index, *fixture)
    root = Path(__file__).resolve().parents[3]
    with tempfile.TemporaryDirectory() as directory:
        lean = Path(directory) / "Oracle.lean"
        lean.write_text("\n".join(declarations + checks) + "\n", encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(lean)], cwd=root, check=True)
    guards = sum(line.startswith("#guard ") for line in checks)
    print(f"CPython {sys.version.split()[0]} zoneinfo, tzdata 2025b: {guards} Lean checks across {len(FIXTURES)} zones")
    print(f"tzdata wheel SHA-256 {WHEEL_SHA256}")


if __name__ == "__main__":
    main()
