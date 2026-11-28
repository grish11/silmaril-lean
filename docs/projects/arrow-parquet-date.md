# Arrow and Parquet scalar date interoperability

Import `Silmaril.Formats.DateInterop.Defs` for adapters on already-decoded
signed date payloads. They use `CivilDate` from the proleptic Gregorian model.
The day count is signed and relative to 1970-01-01. The calendar uses astronomical
year numbering, with year zero immediately before year 1. [Gregorian definitions](../../Silmaril/Numeric/Gregorian/Defs.lean)

| API | Stored value | Admitted epoch days |
| --- | --- | --- |
| `Date32` | Signed Int32 days | −2147483648 through 2147483647 |
| `Date64` | Signed Int64 milliseconds, exactly divisible by 86400000 | −106751991167 through 106751991167 |
| `ParquetDate` | Signed INT32 days with DATE annotation | −2147483648 through 2147483647 |

Arrow uses the `DateUnit.DAY` and `DateUnit.MILLISECOND` cases of its Date
descriptor. Parquet DATE annotates an INT32 day count and uses signed ordering.
The standalone API assumes the caller has already interpreted the physical
payload and selected its date kind. Arrow IPC metadata, Parquet annotation
admission and page decoding are separate layers. [Arrow 26.0.1 Schema.fbs](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Schema.fbs#L241-L254)
· [Parquet format 2.14.0 logical types](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/LogicalTypes.md#date)

The civil encoders reject invalid Gregorian fields before checking the signed
word range. Date64 multiplies in unbounded integers before narrowing. Its
decoder checks the remainder before division, including for negative payloads.
Both raw Int64 endpoints have a nonzero remainder. The extreme admitted
millisecond counts are ±9223372036828800000. The adapter uses uniform days
without timezone or leap-second interpretation.

`ofEpochDay?_isSome_iff` gives the exact closed representability interval.
For Date64, `toEpochDay?_eq_none_iff` characterizes the fractional-day
rejection and `toEpochDay?_eq_some_iff` identifies the exact accepted count.
The `ofCivil?_eq_some_iff` laws give the exact civil and payload inverse
relations. Date32 and Parquet DATE share their executable conversions and
proofs. [Theorem header](../../Silmaril/Formats/DateInterop/Thms.lean)

## Independent fixtures

The harness cross-checks Gregorian coordinates against CPython 3.13.5
`datetime`. For years beyond its native range, it uses `datetime` in a
400-year window and shifts whole Gregorian cycles. PyArrow 26.0.1 independently
validates Date64 remainder rejection, reads back both Arrow IPC streams, and
reads back an INT32 DATE Parquet file. It checks civil conversion directly
where the Python date API admits it and observes raw signed buffers outside
that range. The manifest pins the tool versions, Linux x86-64 wheel and three
artifact hashes. Lean compares against the independently observed scalar
payloads and civil fields. [Fixture manifest](../../scripts/date-interop-oracle/fixtures.json)
· [CPython 3.13.5 datetime](https://github.com/python/cpython/blob/6cb20a219a860eaf687b2d968b41c480c7461909/Modules/_datetimemodule.c)
· [PyArrow 26.0.1](https://pypi.org/project/pyarrow/26.0.1/)

```sh
targets='+Silmaril.Formats.DateInterop.Thms +Silmaril.Formats.DateInterop.Tests +Silmaril.Numeric.Gregorian.Tests'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
python3 -I scripts/date-interop-oracle/check.py
```

The oracle takes `--pyarrow-path` when the pinned wheel has been unpacked
outside the Python environment.
