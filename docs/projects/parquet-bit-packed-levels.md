# Checked Parquet V1 BIT_PACKED levels

Parquet Format **2.14.0** defines the deprecated encoding `BIT_PACKED`
(ID `4`) for repetition and definition levels. A V1 section stores
fixed-width values back to back, from the most significant bit of each
byte to the least significant bit. Given `count` and the bit width `w`
of the maximum level, the section occupies `(count * w + 7) / 8` bytes.
Parquet-java's tag-4 reader takes that many bytes directly, with no
length word. The format specification is pinned at
`04d56f291ff963e98bc37ab8100e2fc133ff583c`. The raw `Encodings.md`
SHA-256 is
`b6b980c67acc14d3e9e4b592c582523b5dc2cc09ad9f90bc2b1912df461e5c88`.
[Wire rule][spec] · [V1 header fields][idl] · [Reference reader extent][reader]

## Reader contract

`BitPackedLevels.readPrefix maxLevel count limits source` reads one
level section and returns its ordered levels and the unchanged byte
suffix. The caller supplies the checked page count, schema maximum,
and input starting at the level section. The reader checks
`maxLevel < 2^31`, `count < 2^31`, and the caller's count and consumed
byte caps before slicing. The extent uses unbounded natural-number
arithmetic. It rejects short input and any decoded code greater than
the supplied maximum. With maximum level zero it consumes no bytes
and returns exactly `count` zeros. With count zero it consumes no
bytes and returns an empty list at any admitted maximum.
`readExact` checks that an already-delimited section has no suffix.

The format describes the final partial byte as padded with zeros.
Parquet-java **1.16.0** emits zero padding and accepts unused low bits of
either value on readback. For example, its reader returns the same
five levels from producer byte `b0` and consumer probe `b7`. This
reader also ignores those unused bits. Its strict extent and level
checks reject two inputs the tested Java reader accepts. Java returns
code 3 from `c0` at maximum level 2 and fills in a final zero for a
short nine-value section that contains bytes for only the first
eight values. Existing scanner profiles and V1 header admission are
outside this standalone codec. [Java tag-4 dispatch][tag] · [Java writer][writer]

## Public Lean laws

- `readPrefix_ok_iff` characterizes admission, exact byte decomposition
  and produced levels. The prefix has the count-derived byte length,
  the suffix concatenates back to the original input, and all returned
  levels are within the schema maximum.
- `Wire.getElem_testBit` and `wireCode_testBit` prove the bit relation
  for every decoded level index and bit index. Bit `j` from a level's
  high end comes from position `i * w + j` of the prefix, with byte
  position `/ 8` and bit position `7 - (% 8)`. The model weights each
  bit by its positional power of two. The executable builds the code
  by shifting the accumulated value left. `position_in_extent` ensures
  that every requested bit addresses an existing prefix byte.
- `readPrefix_zero` gives the explicit zero-maximum behavior.
  `readExact_ok_iff` connects the exact-slice reader to the prefix
  reader with an empty remainder.

## Independent producer and consumer vectors

The oracle uses parquet-java **1.16.0**, commit
`402c3810c372d29603e181771acebfecc71bef61`, to produce seven sections
with `ByteBitPackingValuesWriter` in big-endian mode. Its tag-4
`ValuesReader` reads them back, consumes the exact section bytes, and
leaves the following sentinel `a55a` untouched. The tests include the
specification's `053977` group, a second partial group, partial bytes
at widths one and two, width and count zero, and the signed maximum.
Three additional consumer probes pin Java's observed behavior on
nonzero unused bits, the spare code, and short input without a
following section. Lean checks all seven writer cases, accepts the
padding probe, and rejects the spare code and short input. It also
checks count and byte caps, signed bounds and the exact-slice wrapper.
[Oracle][oracle] · [Vectors][vectors] · [Lean examples][examples]

The columns are kind, case, maximum level, count, section hex,
following bytes hex, and Java readback levels. A dash marks an empty
field. The manifest SHA-256 is
`8a0b54370810890c1a44ea7209ba4792a457a21e1bb66c6da285e56b050032eb`.

| Maven artifact | SHA-256 |
| --- | --- |
| `org.apache.parquet:parquet-column:1.16.0` | `034ec38dc4c58a0677bdaed666c9a7a8c68c269cce0d61dce4b7b49f7a0b9d7e` |
| `org.apache.parquet:parquet-common:1.16.0` | `7c7d120b83c923f9f5044e53518e6e8cc26d7993b89051b2a9979c3afdbc7811` |
| `org.apache.parquet:parquet-encoding:1.16.0` | `da7b8f3a458871e70de6f883539a39d8dc9e8ec67312d3b95ea1dbca4b68f5b3` |
| `org.slf4j:slf4j-api:1.7.33` | `336811855ee97fcd8413343dc42f4d26362502860e8a9193e4db305e3e8ef80a` |
| `org.slf4j:slf4j-nop:1.7.33` | `b3d68ed3f48f89b15e610b42efd72d3413316a07f5ba4ab4589fc449c9cb4beb` |

With these jars in `$jars`, run from the repository root with Java 21.

```sh
set -o pipefail
java -cp "$jars/*" scripts/parquet-bit-packed-levels/BitPackedOracle.java |
  diff -u tests/formats/parquet-bit-packed-levels/parquet-java-1.16.0.tsv -
lake build --wfail +Silmaril.Formats.Parquet.BitPackedLevels.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.BitPackedLevels.Examples
```

[spec]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#L172-L198
[idl]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L698-L718
[reader]: https://github.com/apache/parquet-java/blob/402c3810c372d29603e181771acebfecc71bef61/parquet-column/src/main/java/org/apache/parquet/column/values/bitpacking/ByteBitPackingValuesReader.java#L73-L84
[tag]: https://github.com/apache/parquet-java/blob/402c3810c372d29603e181771acebfecc71bef61/parquet-column/src/main/java/org/apache/parquet/column/Encoding.java#L147-L157
[writer]: https://github.com/apache/parquet-java/blob/402c3810c372d29603e181771acebfecc71bef61/parquet-column/src/main/java/org/apache/parquet/column/values/bitpacking/ByteBitPackingValuesWriter.java#L35-L62
[oracle]: ../../scripts/parquet-bit-packed-levels/BitPackedOracle.java
[vectors]: ../../tests/formats/parquet-bit-packed-levels/parquet-java-1.16.0.tsv
[examples]: ../../Silmaril/Formats/Parquet/BitPackedLevels/Examples.lean
