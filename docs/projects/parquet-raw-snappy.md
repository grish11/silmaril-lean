# Raw Snappy blocks for Parquet

Parquet's `SNAPPY` codec consumes a raw block within a page payload. The
caller supplies the compressed slice and an output budget and remains
responsible for checking the page header's uncompressed size and any
page-level checksum. This profile follows the pinned wire descriptions.
[Coverage matrix](arrow-parquet-coverage.md) · [Parquet 2.14.0 compression][parquet] ·
[Snappy 1.2.2][snappy-wire]

## Wire and codec contract

The preamble gives the uncompressed length as a little-endian base-128
varint. It terminates within five bytes, with at most four payload bits in
the fifth byte. The following tags must account for exactly that many
output bytes. Let `hi` be the tag byte divided by four, rounded down.

| Low two bits | Remaining fields | Output |
| --- | --- | --- |
| 0 with `hi < 60` | `hi + 1` literal bytes | Append the literal. |
| 0 with `hi ≥ 60` | `hi - 59` length bytes, then the literal | The little-endian length field stores length minus one. |
| 1 | One low offset byte | The offset is `256 * (hi / 8) + low` and the length is `hi % 8 + 4`. |
| 2 | Two little-endian offset bytes | Copy `hi + 1` bytes. |
| 3 | Four little-endian offset bytes | Copy `hi + 1` bytes. |

The reader accepts longer encodings of a size that fit these field bounds,
as the pinned Snappy reader does. A copy's offset must be positive and no
larger than the output produced so far. Each copy byte reads that distance
back from the current end, so a copy can read bytes it appended earlier.

`parse limit` gives the tag AST for exactly one block. It checks the preamble
against the budget before reading tags, then checks each tag's contribution
against the remaining output length before reading any literal body.
`decode limit` expands that AST, validating offsets against the live
history. Expansion uses the library's array back-copy and its list semantics.
For a page slice, use `decode`, which rejects trailing bytes.
`decodeMember` and the `Compression.Format` adapter return the unread
suffix for callers working with prefix decoders.

Failures distinguish three cases.

- `malformed` reports a bad preamble, truncated tag, declared-length
  mismatch, invalid offset or trailing bytes. An oversized literal relative
  to the declared remainder fails before its body is read.
- `limited declared limit` reports a syntactically valid preamble that
  exceeds the caller's budget. This check precedes inspection of the body.
- `unsupported framedStream` recognizes the Snappy stream identifier.
  Framed Snappy, Hadoop framing, page slicing and Parquet V1/V2 layout
  are outside the codec.

`encode` emits the shortest preamble and one literal with the shortest
length field for nonempty input. Empty input emits a zero preamble alone.
It reports `limited` for input longer than the wire's uint32 maximum.
The writer does not search for copies. The decoder's budget is a bound on
logical output length. Allocation overhead and execution time are outside
the theorem contract.

## Checked laws and interoperability

Lean proves AST size equals declared size within the budget
(`parseMember_bounds`), exact suffix consumption for the strict parser (`parse_eq_ok_iff`), and length preservation under the tag
denotation (`denotes_length`). `decode_sound` connects successful decoding
to that denotation, exact input consumption and the declared output bound.
[Theorem header][thms]

The Lean regression module is covered by `Silmaril.Formats.+`. It includes
the pinned writer's bytes for empty input, 70 repeated `a` bytes and the byte sequence 0–79, plus authored tag and rejection controls.
[Regression vectors][tests]

The oracle runner builds Google Snappy from the pinned revision with
CMake Release flags and calls `snappy::Compress` and `snappy::Uncompress`.
It compares each side's output bytes against the original input after
decoding the other side's block. It also checks authored overlapping
copy-4, high-offset copy-1, and non-minimal length vectors with both
readers. The generators and controls are under the repository's MIT
license. The Snappy reference implementation uses BSD 3-Clause.
[Oracle runner][oracle] · [Snappy license][license]

Selected fixture fingerprints from the pinned reference on Linux x86-64.
The runner records the remaining input and output digests.

| Generator in the runner | Plaintext SHA-256 | Google Snappy block SHA-256 |
| --- | --- | --- |
| `empty` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | `6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d` |
| `repeat-70` | `6bd5e5034855a11241f0dee8fc72850ffd9955b28347a86428b5fa19119f6ad0` | `c128b86d6ad51425e744c808255f13a142788886e9f104b9d18a3124b088946c` |
| `binary-80` | `c56705fea5b110b8dc63688533ced21167e628017387c885423b835a55edd5ef` | `47be19e6678b9e29acc3811f01d3413bd76c31a419e5f2848a135378c819e5f2` |
| `literal-65537` | `237356e18b503616912abb8ffaed3a72591e397d4ac294c4637917d48a3f529d` | `5570759f67b4f3a045dfa38f93c7eaf898ae3ba7ebc029091e95dc7224e50ce0` |

The writer's interoperability evidence is fixture-based. The reference
writer can choose different tags for the same payload. The runner prints
SHA-256 digests for each plaintext and each encoded block. To reproduce it
from the repository root with Git, CMake, a C++ compiler and Python 3:

```sh
lake build --wfail +Silmaril.Formats.Compression.Snappy.Thms +Silmaril.Formats.Compression.Snappy.Tests
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
python3 -I scripts/snappy-oracle/check.py
```

[parquet]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Compression.md#snappy
[snappy-wire]: https://github.com/google/snappy/blob/6af9287fbdb913f0794d0148c6aa43b58e63c8e3/format_description.txt
[license]: https://github.com/google/snappy/blob/6af9287fbdb913f0794d0148c6aa43b58e63c8e3/COPYING
[thms]: ../../Silmaril/Formats/Compression/Snappy/Thms.lean
[tests]: ../../Silmaril/Formats/Compression/Snappy/Tests.lean
[oracle]: ../../scripts/snappy-oracle/check.py
