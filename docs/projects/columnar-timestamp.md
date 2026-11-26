# Arrow and Parquet timestamp payloads

`Silmaril.Formats.ColumnarTimestamp.Defs` connects the [fixed-point timestamp
core](timestamp.md) and the Gregorian date core to signed 64-bit timestamp
payloads. The logical descriptors are the inputs a future schema adapter
supplies once the wire tags and physical type have been checked.

| Descriptor | Units | Epoch interpretation |
| --- | --- | --- |
| `Arrow.Metadata` | Seconds, milliseconds, microseconds, nanoseconds | An absent or empty timezone gives a local reading. A nonempty timezone selects the Unix epoch and is retained as a display annotation. |
| `Parquet.Metadata` | Milliseconds, microseconds, nanoseconds | `isAdjustedToUTC=true` selects a UTC instant. `false` selects a local reading on uniform 86,400-second days. |

`decode` reads an `Int64` into ticks indexed by the descriptor's kind and
unit. `encode` takes ticks of the same kind, checks exact rescaling into the
target unit, then checks the inclusive signed 64-bit range. `precisionLoss`
means the offset is fractional in the destination unit. `outOfRange` means
the quotient was exact and outside the range. These tests apply on both
sides of the epoch.

For Arrow to Parquet, `parquet` constructs the destination metadata and
`toParquet` converts the payload in the same kind. To retain the original
zone name, keep `timezoneAnnotation` separately since Parquet `TIMESTAMP`
has only the UTC-adjusted flag. For Parquet to Arrow, `arrow` supplies the
canonical annotation `UTC` for an instant and an unset annotation for a
local reading. `toArrow` converts the payload. A successful round trip in
the original unit recovers the signed count and epoch interpretation. An
Arrow zone name discarded at the Parquet boundary is unavailable on return.

`LocalDateTime.ofTicks` splits a local offset into a proleptic Gregorian
date and nanoseconds since local midnight. For example, −1 ns is the last
nanosecond of 1969-12-31. `toTicks?` checks the date and assembles the same
local coordinate. These operations use the local kind throughout.

Wire parsing, unknown enum/union tags, physical type validation and null
handling belong to the metadata and payload codecs. Zone strings are opaque
here, including offsets supplied as strings. This profile has no zone-name or
offset validation, tzdb lookup, DST resolution, leap-second model, ISO 8601
text, legacy ConvertedType reconciliation, or INT96 support.

The specification pins follow the [coverage matrix](arrow-parquet-coverage.md).

- Arrow Columnar 1.5 and IPC V5 as published in Apache Arrow 26.0.1.
  [Pinned `TimeUnit` and `Timestamp` declarations](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Schema.fbs#L256-L397)
- Apache Parquet Format 2.14.0.
  [Pinned `TIMESTAMP` logical type](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/LogicalTypes.md#L361-L476)

## Proofs and checks

The public header is `Silmaril.Formats.ColumnarTimestamp.Thms`.

| Namespace | Theorems |
| --- | --- |
| `ColumnarTimestamp` | `toInt64_eq_ok_iff`, `toInt64_eq_precisionLoss_iff`, `toInt64_eq_outOfRange_iff` |
| `Arrow.Metadata` | `kind_eq_utcInstant_iff`, `parquet_kind`, `encode_decode`, `toParquet_eq_ok_iff`, `toParquet_roundtrip` |
| `Parquet.Metadata` | `kind_eq_utcInstant_iff`, `arrow_kind`, `encode_decode`, `toArrow_eq_ok_iff`, `toArrow_roundtrip` |
| `LocalDateTime` | `toTicks?_ofTicks`, `ofTicks_toTicks?` |

Run from the repository root with the pinned Lean toolchain.

```sh
lake build --wfail +Silmaril.Formats.ColumnarTimestamp.Thms +Silmaril.Formats.ColumnarTimestamp.Tests
make check CHECK_TARGETS='+Silmaril.Formats.ColumnarTimestamp.Thms +Silmaril.Formats.ColumnarTimestamp.Tests'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/columnar-timestamp/Axioms.lean
```

### Independent fixtures

The fixture script regenerates eight small IPC stream and Parquet file pairs
in memory with PyArrow 26.0.1. It checks the Lean mappings against the
metadata and raw signed counts read by PyArrow, before datetime conversion
in Python. It covers all four Arrow units with unset and `Europe/Paris`
annotations, negative ticks, zero and both signed endpoints where the
writer can retain the source unit. Arrow uses IPC V5. Parquet uses version
2.6, uncompressed values, and disables dictionaries, statistics and the
embedded Arrow schema. The expected digest in the script covers the bytes
of every stream and file in generation order, with an eight-byte
little-endian length before each input. The fixtures exercise the logical
payload boundary of the Lean code. [PyArrow release and Apache-2.0 license](https://github.com/apache/arrow/tree/9e5d6978e9acf372cc989aaaf94e863fe8582c90/python)

For the pinned CPython 3.13 Linux x86-64 wheel, run after the Lake build.

```sh
fixture_env=$(mktemp -d)
fixture_wheel="$fixture_env/pyarrow-26.0.1-cp313-cp313-manylinux_2_28_x86_64.whl"
curl -fLsS https://files.pythonhosted.org/packages/96/54/33c2df56948d88a4d83a52999a4a81a4871b2de481ff25ccd6f5ccd2589a/pyarrow-26.0.1-cp313-cp313-manylinux_2_28_x86_64.whl -o "$fixture_wheel"
printf '%s  %s\n' f71221bbc7707e3fad920d0478db9350791d4714ec445299ee0d56559fbc156c "$fixture_wheel" | sha256sum -c &&
python3 -m zipfile -e "$fixture_wheel" "$fixture_env/site" &&
PYTHONPATH="$fixture_env/site" python3 tests/formats/columnar-timestamp/check-fixtures.py
```
