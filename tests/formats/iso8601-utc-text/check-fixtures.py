"""Check exact UTC text using CPython's Gregorian calendar and integer arithmetic."""

from datetime import date, timedelta
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[3]
FIXTURE_SHA256 = "08cf913efb3cbdc54362749dce4f64c3664de28c78407ec1d99796a7c2879c10"
UNITS = {"second": 0, "millisecond": 3, "microsecond": 6, "nanosecond": 9}
EPOCH = date(1970, 1, 1)
ANCHOR = date(2000, 1, 1)
ANCHOR_DAY = (ANCHOR - EPOCH).days
CYCLE_DAYS = (date(2400, 1, 1) - ANCHOR).days
FIRST_DAY = (date(400, 1, 1) - EPOCH).days - CYCLE_DAYS
STOP_DAY = (date(9999, 12, 31) - EPOCH).days + 1
WORD_MIN = -(2**63)
WORD_MAX = 2**63 - 1


def expected(count, width):
    whole_seconds, fraction = divmod(count, 10**width)
    epoch_day, seconds_of_day = divmod(whole_seconds, 86_400)
    # Move into CPython's supported interval by whole Gregorian cycles. This
    # also gives an independent astronomical year for large signed endpoints.
    era, cycle_day = divmod(epoch_day - ANCHOR_DAY, CYCLE_DAYS)
    civil = ANCHOR + timedelta(days=cycle_day)
    year = civil.year + 400 * era
    if not 0 <= year < 10_000:
        return {"yearOutOfRange": year}
    hour, remainder = divmod(seconds_of_day, 3_600)
    minute, second = divmod(remainder, 60)
    suffix = f".{fraction:0{width}d}" if width else ""
    return f"{year:04d}-{civil.month:02d}-{civil.day:02d}T{hour:02d}:{minute:02d}:{second:02d}{suffix}Z"


def fixtures():
    for unit, width in UNITS.items():
        per_second = 10**width
        per_day = 86_400 * per_second
        lower = FIRST_DAY * per_day
        stop = STOP_DAY * per_day
        for count in (
            WORD_MIN, WORD_MAX, -per_day - 1, -per_day, -per_second, -1, 0, 1,
            per_second, per_day - 1, per_day, lower - 1, lower, stop - 1, stop,
        ):
            yield unit, count, expected(count, width)


LEAN = """module

meta import Silmaril.Formats.ISO8601.UTCText.Defs
meta import Silmaril.Numeric.Timestamp.Defs

open Silmaril.Formats.ISO8601 Silmaril.Formats.ISO8601.UTCText Silmaril.Numeric.Timestamp

private meta def checkText (unit : TickUnit) (count : Int)
    (expected : Except UTCText.Error String) : Bool :=
  let ticks : Ticks .utcInstant unit := ⟨count⟩
  match format ticks, expected with
  | .ok actual, .ok golden =>
    actual == golden && (match parse actual with
      | .ok parsed => parsed.offset == .z && parsed.utcTicks.rescale unit == some ticks
      | .error _ => false)
  | .error actual, .error golden => actual == golden
  | _, _ => false

private meta def checkWord (unit : TickUnit) (input : Int64)
    (expected : Except UTCText.Error String) : Bool :=
  match formatInt64 unit input, expected with
  | .ok actual, .ok golden => actual == golden && parseInt64 actual unit == .ok input
  | .error actual, .error golden => actual == golden
  | _, _ => false
"""


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    cases = list(fixtures())
    digest = hashlib.sha256(json.dumps(cases, separators=(",", ":")).encode()).hexdigest()
    assert digest == FIXTURE_SHA256, f"fixture SHA-256 {digest}"
    checks = [LEAN]
    word_checks = 0
    for unit, count, golden in cases:
        if isinstance(golden, str):
            result = f"(.ok {json.dumps(golden)})"
        else:
            result = f"(.error (.yearOutOfRange ({golden['yearOutOfRange']})))"
        checks.append(f"#guard checkText .{unit} ({count}) {result}")
        if WORD_MIN <= count <= WORD_MAX:
            checks.append(f"#guard checkWord .{unit} ({count}) {result}")
            word_checks += 1
    with tempfile.TemporaryDirectory() as temporary:
        driver = Path(temporary) / "Fixtures.lean"
        driver.write_text("\n".join(checks) + "\n", encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(driver)], cwd=ROOT, check=True)
    print(f"CPython 3.13.5: {len(cases)} exact tick checks and {word_checks} signed Int64 checks passed")
    print(f"Fixture SHA-256 {digest}")


if __name__ == "__main__":
    main()
