# Transmitted Zstandard FSE normalized counts

`FseTable.NCount.read` reads one RFC 8878 §4.1.1 count description
at the front of an input. The accuracy log is five plus the first
four bits. The reader then tracks the remaining normalized mass.
For each weight, it reads the low field least-significant bit
first. The cutoff determines whether the field ends there or
requires one more bit. The decoded integer minus one is the
signed weight. A weight of −1 contributes one state. A zero
weight requires a two-bit repeat group. Groups of three extend
the run until a group of zero, one, or two terminates it.
[RFC 8878 wire description][rfc] · [Definitions][defs]

The reader checks the caller's byte cap before each field. The
cap is intersected with 512 bytes. Accuracy and symbol caps are
those of the FSE table builder, with upper bounds of 9 and 256.
The caller can also require an exact symbol count. The reader
stops at exact normalized mass and requires at least two active
symbols. `readTable` passes the checked distribution to the
bounded table builder and returns the same prefix and remainder.
[Table builder][builder]

The result records consumed bits, rounded-up bytes, and the
untouched suffix. Unused high bits of the last touched byte are
discarded and can have any value. `read_sound` proves the count
grammar and exact byte split, including the rounded boundary,
symbol and accuracy limits, optional symbol equality, and exact
mass. `readTable_sound` adds the table denotation and well-formed
state intervals from the table builder. [Theorem header][thms]

Sequence and frame dispatch are outside this increment. The
existing frame profile retains its strict distance/window rule.
Parquet ZSTD remains unsupported. [Frame profile][frame]

## Independent differential

The oracle builds libzstd v1.5.7 at
`f8745da6ff1ad1e7bab384bd1f9d742439278e99`. It writes fixture
prefixes with `FSE_writeNCount`, then uses `FSE_readNCount` and
`FSE_buildDTable_wksp` to check the exact byte count, signed
weights, and every table row against Lean. It puts a distinct
byte suffix after each prefix to check preservation. It also
sets the two unused high bits of the even fixture to one and
checks the same result. [Pinned source][zstd] · [Oracle runner][oracle]

| Fixture | Bits | Bytes | States | Prefix SHA-256 |
| --- | ---: | ---: | ---: | --- |
| even | 14 | 2 | 32 | `181b942b1387cb99ca75d465098fdb0a07d8e5772d70cf771e5fd94353c8fb52` |
| byte-aligned | 16 | 2 | 32 | `7429df452cb03e42bb9a988972202c41fcc100bb1e8a7c52805b733919b73e87` |
| skew | 13 | 2 | 32 | `f4e15c621abef7aabba8bdc21c1f6321d4e60650dfbc5052ef94d983be09564e` |
| short-zero-run | 31 | 4 | 32 | `440c8171444c3d2fae2d64785d127a675bd733a8e6b4ae067a24edd9932193e9` |
| long-zero-run | 183 | 23 | 32 | `9c75438722fd704927f3716795e1a16d181fba0dad6f89c81fd4a6e730981218` |
| all-low | 116 | 15 | 32 | `5322fecfc92a5e3248a297a3df3eddfb9bd9049504272e4f572b87fa36d4b3bd` |
| largest-table | 34 | 5 | 512 | `3508357a261035231153f9604094960f121cd739d0d21f2c18c3c3e3abe2a68a` |
| middle-log | 52 | 7 | 128 | `b7c9f16c47c3e1758ce377d2f9a695916c75569701e9745cc98cffa61f79e786` |

Both implementations reject every proper prefix of the even
fixture and lengths zero through seven of the 23-byte long
zero-run fixture. At lengths eight through 22, pinned libzstd
returns different shorter distributions. For example, at
length eight it reports five consumed bytes and 81 symbols.
Lean rejects all those truncations because the zero run has
no terminating group in the available bits. The oracle also
checks byte, symbol, and log caps, an incorrect expected symbol
count, and a singleton distribution in Lean. [Lean regressions][tests]

```sh
lake build --wfail +Silmaril.Formats.Compression.Zstd.FseTable.NCount.Thms +Silmaril.Formats.Compression.Zstd.FseTable.NCount.Tests
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
python3 -I scripts/zstd-ncount-oracle/check.py
```

[rfc]: https://www.rfc-editor.org/rfc/rfc8878#section-4.1.1
[builder]: zstd-fse-tables.md
[frame]: zstd-rle-frame.md
[defs]: ../../Silmaril/Formats/Compression/Zstd/FseTable/NCount/Defs.lean
[thms]: ../../Silmaril/Formats/Compression/Zstd/FseTable/NCount/Thms.lean
[tests]: ../../Silmaril/Formats/Compression/Zstd/FseTable/NCount/Tests.lean
[oracle]: ../../scripts/zstd-ncount-oracle/check.py
[zstd]: https://github.com/facebook/zstd/tree/f8745da6ff1ad1e7bab384bd1f9d742439278e99
