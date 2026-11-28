"""Independent CPython 3.13.5 reference for signed Gregorian month bounds."""

import calendar
from datetime import date
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
TESTS = ROOT / "Silmaril/Formats/ISO8601/Month/Tests.lean"
EPOCH = date(1970, 1, 1)
CYCLE_DAYS = (date(2400, 1, 1) - date(2000, 1, 1)).days
assert CYCLE_DAYS == 146097

# Both endpoints in each of these vectors are native datetime.date values.
DATETIME_CASES = [(1, 1), (1900, 2), (1969, 12), (1970, 1), (1997, 7),
                  (2000, 2), (2024, 2), (2100, 2), (9999, 11)]
# These require at least one endpoint outside datetime.date's year domain.
EXTENDED_YEAR_CASES = [(-1, 12), (0, 1), (0, 2), (0, 3), (9999, 12), (10000, 1)]


def datetime_start(year, month):
    return (date(year, month, 1) - EPOCH).days


def shifted_start(year, month):
    cycles, phase = divmod(year - 2000, 400)
    return datetime_start(2000 + phase, month) + cycles * CYCLE_DAYS


def observe(cases, start_day):
    fixtures = []
    for year, month in cases:
        start = start_day(year, month)
        next_year, next_month = (year + 1, 1) if month == 12 else (year, month + 1)
        stop = start_day(next_year, next_month)
        length = calendar.monthrange(year, month)[1]
        assert stop - start == length
        spelling = f"{year:04d}-{month:02d}" if 0 <= year <= 9999 else None
        fixtures.append({"year": year, "month": month, "text": spelling,
                         "start": start, "stop": stop, "days": length})
    return fixtures


def guard(fixture):
    text = fixture["text"]
    text_term = "none" if text is None else f'(some "{text}")'
    return (f'#guard observes ({fixture["year"]}) {fixture["month"]} '
            f'({fixture["start"]}) ({fixture["stop"]}) {text_term}')


def main():
    expected = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert sys.implementation.name == "cpython"
    assert ".".join(map(str, sys.version_info[:3])) == expected["cpython"], sys.version
    calendar_source = Path(calendar.__file__).read_bytes()
    assert hashlib.sha256(calendar_source).hexdigest() == expected["calendar_source_sha256"]
    for year, month in DATETIME_CASES:
        assert shifted_start(year, month) == datetime_start(year, month)
    observed = {
        "datetime": observe(DATETIME_CASES, datetime_start),
        "extended_year": observe(EXTENDED_YEAR_CASES, shifted_start),
    }
    assert observed == expected["fixtures"], json.dumps(observed, indent=2)

    checks = [guard(fixture) for group in observed.values() for fixture in group]
    with tempfile.TemporaryDirectory(prefix="iso8601-month-") as directory:
        harness = Path(directory) / "Oracle.lean"
        harness.write_text(TESTS.read_text(encoding="utf-8") + "\n" + "\n".join(checks) + "\n",
                           encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(harness)], cwd=ROOT, check=True)
    print(f"PASS {len(observed['datetime'])} native datetime month fixtures and "
          f"{len(observed['extended_year'])} extended-year month fixtures")


if __name__ == "__main__":
    main()
