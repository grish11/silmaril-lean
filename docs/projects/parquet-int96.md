# Legacy Parquet INT96 timestamp payloads

`Silmaril.Formats.Parquet.Int96.Defs` handles the 12-byte PLAIN physical
payload used by the `NanoTime` writer convention. The first eight bytes are
a little-endian nanosecond-of-day word, and the last four are a
little-endian, signed two's-complement Julian day. The accepted subday
range is 0 through 86,399,999,999,999 nanoseconds. `Payload.decode?` rejects
any other length or subday, including a negative word emitted as a signed
`long`. Every signed 32-bit day is representable. Encoding checks the day
before narrowing when it starts from an epoch day or civil timestamp.

`Policy.prolepticUtc` selects UTC instant coordinates and
`Policy.prolepticLocal` selects unzoned wall-clock coordinates. Both use a
proleptic Gregorian calendar with uniform 86,400-second days. The policy
comes from the caller's writer and dataset context. `toTicks` subtracts
Julian day 2,440,588 for 1970-01-01 and combines the result with the subday
in unbounded integer arithmetic. `ofTicks?` uses Euclidean division. For
example, −1 ns splits into day 2,440,587 and the last nanosecond of that
day. `toGregorian` and `ofGregorian?` expose the same proleptic date and
subday coordinates. `toInt64` additionally checks target-unit precision
and signed 64-bit range through the shared timestamp core.

This profile interprets the stored day on the chosen proleptic scale.
Spark legacy calendar rebasing, writer metadata classification, time-zone
lookup and adjustment, and leap seconds are outside the profile. A PLAIN
adapter can pass one exact 12-byte chunk to `Payload.decode?`, then supply
an independently chosen `Policy` to `Payload.toTicks`. Page decoding and
byte slicing stay with the physical codec. A modern timestamp adapter can
consume those typed ticks through its checked `Int64` encoder.

## References

- Parquet Format 2.14.0 PLAIN encodings. [Pinned `Encodings.md`](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#L53-L66)
- parquet-java 1.16.0 signed fields and field order. [Pinned `NanoTime.toBinary` and `fromBinary`](https://github.com/apache/parquet-java/blob/402c3810c372d29603e181771acebfecc71bef61/parquet-column/src/main/java/org/apache/parquet/example/data/simple/NanoTime.java#L27-L65)
- Spark 4.1.0 writer layout and rebase selection. [Pinned write path](https://github.com/apache/spark/blob/e221b56be7b6d9e48e107fc4d1cf0c15f02700f8/sql/core/src/main/scala/org/apache/spark/sql/execution/datasources/parquet/ParquetWriteSupport.scala#L239-L253)
- Apache Arrow 26.0.1 legacy timestamp writer and reader used for the oracle. [Pinned source](https://github.com/apache/arrow/tree/9e5d6978e9acf372cc989aaaf94e863fe8582c90/cpp/src/parquet/arrow)

## Proofs and checks

The public theorem header `Silmaril.Formats.Parquet.Int96.Thms` provides
`Payload.encode_length`, `decode_encode`, `encode_of_decode` and
`decode_eq_none_iff` for the wire boundary. `ofEpochDay_eq_some_iff` and
`ofTicks_eq_none_iff` describe the signed day check. `toTicks_ofTicks`,
`ofTicks_toTicks`, and `toInt64_eq_ok_iff` give preservation and exact
round trips at the tick boundary. `ofGregorian_toGregorian` and
`toGregorian_ofGregorian` give the civil coordinate round trips on their
accepted domain.

```sh
lake build --wfail +Silmaril.Formats.Parquet.Int96.Thms +Silmaril.Formats.Parquet.Int96.Tests
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Int96.Thms +Silmaril.Formats.Parquet.Int96.Tests'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-int96/Axioms.lean
```

The independent check uses the Apache-2.0 parquet-testing fixture
`int96_from_spark.parquet` from commit `0e00127a431f83388d38eebb22cf644d06e86a15`.
The file identifies Spark 3.4.3 and parquet-mr 1.13.1. Its SHA-256 is
`e769aaa996dee57f1104470dcce16d6871cd720d314c13361db16bf9e49f5c97`.
The script takes five INT96 words from the pinned file's Snappy dictionary
page. For the four valid words, Lean's decoding, exact tick denotation and
re-encoding are compared with the bytes and PyArrow's integer observations.
The fifth has a negative subday and exercises rejection. The script also
writes two uncompressed PLAIN files with PyArrow 26.0.1's legacy INT96 option
and checks their 11 values, including pre-epoch values, a date in 1500 and
the two signed `Int64` nanosecond endpoints. For each valid word the script
checks the integer coordinate and byte round trip under both explicit
policies. It compares the stored proleptic Gregorian date with Python’s
Gregorian date calculation, including the pre-1582 word. The generated
digest covers the two files in order, with an eight-byte little-endian
length before each file. Page extraction is specific to the pinned fixtures.
[Pinned Spark file](https://github.com/apache/parquet-testing/blob/0e00127a431f83388d38eebb22cf644d06e86a15/data/int96_from_spark.parquet)

Run the oracle after building the Lean targets. These commands use the
pinned CPython 3.13 Linux x86-64 wheel.

```sh
(
  set -eu
  int96_env=$(mktemp -d)
  int96_wheel="$int96_env/pyarrow-26.0.1-cp313-cp313-manylinux_2_28_x86_64.whl"
  curl -fLsS https://files.pythonhosted.org/packages/96/54/33c2df56948d88a4d83a52999a4a81a4871b2de481ff25ccd6f5ccd2589a/pyarrow-26.0.1-cp313-cp313-manylinux_2_28_x86_64.whl -o "$int96_wheel"
  printf '%s  %s\n' f71221bbc7707e3fad920d0478db9350791d4714ec445299ee0d56559fbc156c "$int96_wheel" | sha256sum -c
  python3 -m zipfile -e "$int96_wheel" "$int96_env/site"
  curl -fLsS https://raw.githubusercontent.com/apache/parquet-testing/0e00127a431f83388d38eebb22cf644d06e86a15/data/int96_from_spark.parquet -o "$int96_env/spark.parquet"
  PYTHONPATH="$int96_env/site" python3 tests/formats/parquet-int96/check-fixtures.py "$int96_env/spark.parquet"
)
```
