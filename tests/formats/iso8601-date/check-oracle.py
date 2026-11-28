"""Compare the ISO ordinal and week profiles against CPython 3.13.5 datetime."""

from datetime import date, timedelta
import os
from pathlib import Path
import subprocess
import sys
import tempfile


def main():
    assert sys.version_info[:3] == (3, 13, 5), sys.version
    epoch = date(1970, 1, 1)
    years = (1582, 1899, 1900, 1969, 1970, 1999, 2000, 2004, 2009, 2014,
             2015, 2019, 2020, 2021, 2026, 2099, 2100, 2399, 2400)
    samples = {date(year, 1, 1) + timedelta(days=offset)
               for year in years for offset in range(-4, 8)}
    samples.update(date.fromisoformat(value) for value in (
        "0001-01-01", "1500-03-01", "1900-02-28", "1900-03-01", "2000-02-29",
        "2000-12-31", "2020-12-31", "9999-12-31",
    ))
    declarations = [
        "module",
        "import Silmaril.Formats.ISO8601.Date.Defs",
        "meta import Silmaril.Formats.ISO8601.Date.Defs",
        "meta import Silmaril.Numeric.Gregorian.Defs",
        "meta import Silmaril.Numeric.Gregorian.ISODate.Defs",
        "open Silmaril.Formats.ISO8601 Silmaril.Numeric.Gregorian",
    ]
    checks = []
    for civil in sorted(samples):
        day = (civil - epoch).days
        ordinal = (civil - date(civil.year, 1, 1)).days + 1
        wk = civil.isocalendar()
        assert date.fromisocalendar(*wk) == civil
        for kind, text in (
            ("Ordinal", f"{civil.year:04d}-{ordinal:03d}"),
            ("Week", f"{wk.year:04d}-W{wk.week:02d}-{wk.weekday}"),
        ):
            checks.extend([
                f'#guard (parse{kind}Date? "{text}").bind {kind}Date.toEpochDay? = some ({day})',
                f'#guard render{kind}Date? ({kind}Date.ofEpochDay ({day})) = some "{text}"',
                f'#guard (parse{kind}Date? "{text}").bind {kind}Date.toCivil?'
                f' = some ⟨{civil.year}, {civil.month}, {civil.day}⟩',
            ])
    for year in (1900, 2019, 2021, 2100):
        assert (date(year, 1, 1) + timedelta(days=365)).year != year
        checks.append(f'#guard parseOrdinalDate? "{year:04d}-366" = none')
    for year in (2014, 2016, 2019, 2021):
        try:
            date.fromisocalendar(year, 53, 1)
        except ValueError:
            checks.append(f'#guard parseWeekDate? "{year:04d}-W53-1" = none')
        else:
            raise AssertionError(f"{year} has week 53")

    root = Path(__file__).resolve().parents[3]
    with tempfile.TemporaryDirectory() as tmp:
        lean = Path(tmp) / "Oracle.lean"
        lean.write_text("\n".join(declarations + checks) + "\n", encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(lean)], cwd=root, check=True)
    print(f"CPython {sys.version.split()[0]}: {len(checks)} Lean checks on {len(samples)} dates and eight invalid dates")


if __name__ == "__main__":
    main()
