# Zstandard interleaved FSE Huffman weights

`Huffman.FseWeights.read` reads the exact compressed Huffman description
through the checked prefix and emits the explicit weights in symbol order.
It returns the number of descriptor bytes consumed and the original
literal-stream suffix. The caller supplies a byte limit and an explicit-weight
limit, intersected with the RFC ceiling of 255 explicit weights. The remaining
weight budget decreases even for transitions that consume zero bits.
[RFC 8878 §4.2.1.2][rfc] · [Definitions][defs] · [Prefix profile][prefix]

State1 starts as the active state. At each step the active row emits its
symbol. If its full-width field fits, the decoder reads it in reverse MSB
order, adds it to the row baseline, then swaps active and waiting states.
A field of exactly the remaining width fits, including a zero-width field
on an empty cursor.

The first field strictly wider than the remaining bits is terminal. The
missing low bits are conceptually zero and the updated state has no future
use, so the implementation need not calculate it. The last two emitted
symbols come from the active and waiting rows in that order. No field is
needed from the waiting row. Both symbols must fit the remaining weight
budget. A short declared description, absent or zero end marker, or
incomplete initial state remains a prefix error. This format has no
independent explicit-weight count, so a shorter, consistently redeclared
description with a valid marker can encode a different list.
[RFC terminal rule][rfc] · [Pinned libzstd tail loop][native]

`read_sound` proves the exact alternating trace, first overflow boundary,
ordinary next-state bounds, and the exact byte extent. Success returns at
least two weights, at most the checked cap, each in the range 0 through 11.
`emits_unique` proves the initialized states and bits determine the weight
list. `suffix_exact` proves the byte remainder is unchanged. The output
is suitable for the separate `Weights.complete` validity check and last
weight inference. This API ends at explicit weight emission, before
tree completion or literal, frame, and Parquet dispatch.
[Theorems][thms] · [Tree completion][weights]

## Pinned differential

The oracle builds libzstd v1.5.7 at
`f8745da6ff1ad1e7bab384bd1f9d742439278e99`. On the same two
library-produced literal payloads as the prefix layer, it compares every
explicit weight with `FSE_decompress_wksp_bmi2` and with `HUF_readStats`
before the inferred final weight. It checks both the consumed extent and
the literal suffix, and rejects one-less caller caps.
[Pinned source][zstd] · [Runner][oracle] · [Frame hashes][weights]

| Tree symbols | Explicit weights | Explicit weight bytes SHA-256 |
| --- | --- | --- |
| 160 | 159 | `44779bbc8428b04737b4f5b342a7907b2aba13114061e0096d0acf19182da647` |
| 256 | 255 | `a8c0cf05683fc5fde5585834637c3958d1632cf61edcda4b1f5427c30affe2a4` |

The synthetic cases use pinned `FSE_writeNCount` output for log-5 counts
`[16,16]` and log-6 counts `[15,16,33]`. The reverse fields are hand-built.
Both readers reject truncated descriptors, a zero marker and incomplete
initialization. The generic native FSE decoder emits 256 weights for the
oversized control, while the native Huffman reader and Lean enforce the
255-weight maximum. [Regressions][tests]

| Terminal case | Description hex | Output |
| --- | --- | --- |
| Overflow on State1 | `04 10 3f 03 04` | `0 1` |
| Exact field, then overflow on State2 | `04 10 3f 07 08` | `0 1 0` |
| Nonempty short field | `05 01 45 3f 17 40` | `0 1` |
| Zero-bit update before overflow | `05 01 45 3f 85 1f` | `2 1 0` |

```sh
lake build --wfail +Silmaril.Formats.Compression.Zstd.Huffman.FseWeights.Tests +Silmaril.Formats.Compression.Zstd.Huffman.FsePrefix.Tests +Silmaril.Formats.Compression.Zstd.Huffman.Weights.Tests
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
python3 -I scripts/zstd-huffman-fse-weights-oracle/check.py
```

[rfc]: https://www.rfc-editor.org/rfc/rfc8878#section-4.2.1.2
[defs]: ../../Silmaril/Formats/Compression/Zstd/Huffman/FseWeights/Defs.lean
[thms]: ../../Silmaril/Formats/Compression/Zstd/Huffman/FseWeights/Thms.lean
[tests]: ../../Silmaril/Formats/Compression/Zstd/Huffman/FseWeights/Tests.lean
[prefix]: zstd-huffman-fse-prefix.md
[weights]: zstd-huffman-weights.md
[oracle]: ../../scripts/zstd-huffman-fse-weights-oracle/check.py
[zstd]: https://github.com/facebook/zstd/tree/f8745da6ff1ad1e7bab384bd1f9d742439278e99
[native]: https://github.com/facebook/zstd/blob/f8745da6ff1ad1e7bab384bd1f9d742439278e99/lib/common/fse_decompress.c#L219-L233
