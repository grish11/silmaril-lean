# Checked Date64 IPC to Date32 payloads

`Date32.widen` converts every signed Int32 day to an exact signed Int64
millisecond count. `Date64.narrow?` checks divisibility by 86,400,000
milliseconds per day and the inclusive signed Int32 range
−2147483648 through 2147483647. Both units count from 1970-01-01 in the
existing proleptic Gregorian model. The result is also a Parquet DATE
payload, whose physical type is signed INT32 days.
[Arrow 26.0.1 Schema.fbs](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Schema.fbs)
· [Parquet 2.14.0 DATE](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/LogicalTypes.md#date)
· [Scalar laws](../../Silmaril/Formats/DateInterop/Conversion/Thms.lean)

`Arrow.DateStream.Narrow.read` first admits the complete stream through
the existing single-field, little-endian V5 DATE reader, then requires
its normalized MILLISECOND unit. It preserves the field name, declared
nullability, batch boundaries including empty batches, and each ordered
nullable slot. Successful output contains exact Date32 payloads. It can
be mapped back to the original nested Gregorian observation with
`civilBatches`.
[IPC profile](arrow-date-stream.md)
· [Pinned IPC specification](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst)
· [Executable API](../../Silmaril/Formats/Arrow/DateStream/Narrow/Defs.lean)

Reader errors take precedence over all post-admission errors. A present
Date64 word with a fractional day therefore retains its existing indexed
`.reader (.batch batch (.values (.nonWholeDay slot)))` error even when
an earlier batch contains an out-of-range whole day. A successfully
admitted Date32 stream returns `.wrongUnit .day`. A Date64 stream with an
unrepresentable whole day returns `.outOfRange batch slot day` at the
first such slot in batch order. Indices are zero-based. The helper's
`.invalidCivil` case is unreachable through the checked reader. Every
failure returns a typed error as the complete result.

`Date64.narrow?_widen` and `Date32.widen_of_narrow?` prove the inverse
laws. `Date64.narrow?_eq_civil` connects the direct word conversion to
the civil-date path. The stream laws `read_ok_iff` and
`read_outOfRange_iff` characterize the exact nested slots and the first
range failure after representable prefixes. `read_of_reader_error` and
`read_ne_invalidCivil` cover stage precedence and civil validity.
[Stream theorem header](../../Silmaril/Formats/Arrow/DateStream/Narrow/Thms.lean)

## Verification

The oracle writes and rereads six IPC streams using CPython 3.13.5 and
PyArrow 26.0.1. PyArrow independently widens raw Date32 words and checks
the original signed words by viewing the native storage type. The
fixtures cover both signed Int32 endpoints, negative epoch, leap day,
a UTF-8 label, nulls, an empty batch, the adjacent rejected days,
a late negative remainder, competing range and remainder errors, and
an admitted Date32 stream. The fractional examples use raw Date64
millisecond words to exercise the typed rejection.
[Fixture hashes](../../scripts/arrow-date64-narrow-oracle/fixtures.json)
· [Oracle](../../scripts/arrow-date64-narrow-oracle/check.py)

```sh
targets='+Silmaril.Formats.DateInterop.Conversion.Thms +Silmaril.Formats.Arrow.DateStream.Narrow.Thms +Silmaril.Formats.Arrow.DateStream.Narrow.Tests +Silmaril.Formats.Arrow.DateStream.Tests +Silmaril.Formats.DateInterop.Tests'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
python3 -I scripts/arrow-date64-narrow-oracle/check.py
```

Use `--pyarrow-path` for a separately unpacked pinned wheel.
