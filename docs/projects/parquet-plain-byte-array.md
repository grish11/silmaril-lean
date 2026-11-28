# Bounded Parquet PLAIN BYTE_ARRAY

`Silmaril.Formats.Parquet.Plain.ByteArray.Defs` reads and writes an exact
PLAIN scalar slice in `Silmaril.Formats.Bytes`. Call `decode limits count
source` with the number of present values, or `encode limits values` with
an ordered list of byte strings. The theorem header is
`Silmaril.Formats.Parquet.Plain.ByteArray.Thms`.

Apache Parquet Format **2.14.0**, commit
`04d56f291ff963e98bc37ab8100e2fc133ff583c`, specifies a four-byte
little-endian length before each value. The raw `Encodings.md` SHA-256 is
`b6b980c67acc14d3e9e4b592c582523b5dc2cc09ad9f90bc2b1912df461e5c88`.
[PLAIN wire specification][spec] · [parquet-java 1.16.0 PLAIN codecs][java]

## Checked profile

- Length words represent nonnegative signed 32-bit integers. The high bit
  must be clear. Both directions enforce lengths from zero to `2^31 - 1`
  along with the caller's per-value limit. The total byte limit includes
  every four-byte length word and every value byte.
- Empty values each have a zero length word. Null slots are represented by
  definition levels and have no PLAIN entry. Zero present values require an
  empty scalar slice. The reader rejects short length words, truncated
  value bodies, and any bytes left after the expected count. No padding is
  consumed. Extent arithmetic uses `Nat`, and the reader checks the extent
  before copying each value. The writer checks both limits before packing.
- Bytes are opaque. This reader preserves embedded zero octets and malformed
  UTF-8, leaving STRING and other logical annotation interpretation to a
  separate adapter.

A flat PLAIN page callback can use `ScalarPage.decode (.byteArray limits)
params pageLimits body` for `Footer.PhysicalType.byteArray`. Here `limits`
apply to the decoded scalar slice and each individual value, and `pageLimits`
apply to the full page and definition levels. The result has type
`List (Option Bytes)` on success, with a present empty byte string distinct
from a null slot. The existing [header and body mapping][scalar] applies to
both page versions. `ScalarPage.readPlain_size` and `decode_sound` express
the size using the decoded values for BYTE_ARRAY. Their fixed-width and
Boolean cases retain their count-based formulas. Frame traversal, CRC, and
row-group assembly stay with the caller.

## Proofs

`decode_ok_iff` characterizes the exact input as the concatenation of the
length words and payloads for the returned values, with exact count and both
limits. `encode_ok_iff` characterizes the same wire and bounds for output.
`decode_size` and `encode_size` give the sum of `4 + value.length` over the
ordered values. `decode_encode` and `encode_decode` prove round trips for
all accepted inputs under the same limits.

## Independent fixtures

The [fixture manifest][vectors] contains four uncompressed, non-dictionary
PLAIN pages from PyArrow **26.0.1**, Arrow commit
`9e5d6978e9acf372cc989aaaf94e863fe8582c90`. The [oracle][py] reads the
files back, checks that the column is unannotated binary, and uses Apache
Thrift **v0.25.0** to extract the original bodies and scalar slices. For both
V1 and V2 it writes a mixed page with a present empty value, nulls, `c3a9`,
`ff0080`, and `7879`, plus an all-null page. The [Java oracle][oracle-java]
round-trips the mixed page's present values through parquet-java **1.16.0**
and produces the same scalar bytes. This cross-check exercises its scalar
reader and writer. The V1 and V2 page production comes from PyArrow.

The TSV columns are page version, fixture name, slot count, null count,
raw definition byte count, on-disk page body, and scalar suffix. A dash
marks an empty byte slice. The manifest SHA-256 is
`78579fd384ec255400d31aa206e875122a5a4dd8f7df29f0dc38ab9aa6f672fc`.
The [Lean examples][examples] check the manifest, both directions and both
page versions, a 256-byte value for little-endian length order, and
rejection for count, size, and extent violations.

Use the pinned Python wheels and Thrift archive from the [flat-page
recipe][flat], and the pinned Maven jars from the [PLAIN recipe][plain].
With the Python packages on the import path and `jars` set to the Maven
jar directory, run the following from the repository root.

```sh
set -o pipefail
fixture=tests/formats/parquet-plain-byte-array/pyarrow-26.0.1.tsv
python3 scripts/parquet-plain-byte-array/PyArrowOracle.py | diff -u "$fixture" -
java -cp "$jars/*" scripts/parquet-plain-byte-array/PlainByteArrayOracle.java |
  diff -u <(awk -F '\t' '$1 == "1.0" && $2 == "mixed" {print $7}' "$fixture") -
lake build --wfail +Silmaril.Formats.Parquet.Plain.ByteArray.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.Plain.ByteArray.Examples
```

[spec]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#plain-plain--0
[java]: https://github.com/apache/parquet-java/tree/402c3810c372d29603e181771acebfecc71bef61/parquet-column/src/main/java/org/apache/parquet/column/values/plain
[scalar]: parquet-scalar-page.md#header-and-body-adapter
[flat]: parquet-flat-page.md#independent-page-fixtures
[plain]: parquet-plain.md#independent-fixtures
[vectors]: ../../tests/formats/parquet-plain-byte-array/pyarrow-26.0.1.tsv
[py]: ../../scripts/parquet-plain-byte-array/PyArrowOracle.py
[oracle-java]: ../../scripts/parquet-plain-byte-array/PlainByteArrayOracle.java
[examples]: ../../Silmaril/Formats/Parquet/Plain/ByteArray/Examples.lean
