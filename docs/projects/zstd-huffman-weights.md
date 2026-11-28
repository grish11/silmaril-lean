# Zstandard Huffman tree completion

`Huffman.Weights.complete` takes an already decoded list in literal-symbol
order. The checker allows at most 255 explicit weights plus one inferred
weight, and intersects the RFC depth ceiling of 11 with the caller's depth
cap. The caller may further lower the symbol cap. It checks the list extent
and each weight before computing powers of two. Zero weights preserve
symbol indices and contribute no slots.
[RFC 8878 §§4.2.1–4.2.1.3][rfc] · [Definitions][defs]

The explicit slot mass must be positive. The checker takes the next strictly
larger power of two and requires the remaining mass to be a single positive
power of two. Its exponent determines the final weight. The completed
deepest rank must contain at least two entries and have even population.
`Weights.complete_sound` proves the exact append, mass and rank rules, and
the symbol, weight and depth bounds. `Weights.complete_of_valid` proves
that any valid completion with that mass witness is returned, so the final
weight and depth are unique. [Theorem header][thms]

The direct parser still checks its 65-byte and 129-symbol ceilings and
rejects FSE descriptions. It uses the shared completer after extracting
the nibbles. `SingleStream.buildGeneral` uses the existing canonical
placement with the general bounds. Its soundness theorem gives the
same interval relation used by the direct builder. This slice starts
after weight extraction. FSE entropy reading, literal-section dispatch,
treeless state, frame decoding and Parquet activation remain separate.
[Direct parser][direct] · [Canonical builder][table]

## Pinned differential

The runner builds libzstd v1.5.7 at
`f8745da6ff1ad1e7bab384bd1f9d742439278e99`. It compresses deterministic
skewed byte samples, checks full-frame expansion in libzstd, and extracts
fresh FSE weight descriptions from four-stream literal sections. Native
`HUF_readStats` supplies the explicit weights to Lean. The runner compares
Lean's inferred last weight, depth and full tree with the native result
and checks that the shared builder places every positive-weight symbol,
including literal 255 in the full-alphabet case. This comparison uses native
entropy decoding to obtain the explicit weights. [Pinned source][zstd] · [Runner][oracle]

| Symbols | Depth | Description bytes | Frame SHA-256 | Description SHA-256 |
| --- | --- | --- | --- | --- |
| 160 | 10 | 36 | `11c00a2d60db5362a72b7a014f07984b0832e1e323b138200194ae3e0a61a229` | `ccf34a085d6cadb19e7680e300043fd1e6ef8cc71c9ea0ff7b4203fbd2a02184` |
| 256 | 11 | 36 | `41cf51c4513aef112c218d0202dc21a2ba336cdfa9b9c2b0e944fde83b6fd75b` | `5da82e8ceb7e92b11f9cf9ad5eb80f96648eec4a7094268d1d702c0953b0cbf7` |

Both implementations reject zero mass, a non-power remainder and a missing
deepest rank. Lean also checks reduced caller caps and rejects 256 explicit
weights. Pinned `HUF_readStats` accepts a depth-12 description, which Lean
rejects under the RFC ceiling. [Lean regressions][tests] · [Runner][oracle]

```sh
lake build --wfail +Silmaril.Formats.Compression.Zstd.Huffman.Weights.Tests +Silmaril.Formats.Compression.Zstd.Huffman.DirectWeights.Tests +Silmaril.Formats.Compression.Zstd.Huffman.SingleStream.Tests +Silmaril.Formats.Compression.Zstd.Huffman.FourStream.Tests
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
python3 -I scripts/zstd-huffman-weights-oracle/check.py
python3 -I scripts/zstd-huffman-direct-oracle/check.py
```

[rfc]: https://www.rfc-editor.org/rfc/rfc8878#section-4.2.1
[defs]: ../../Silmaril/Formats/Compression/Zstd/Huffman/Weights/Defs.lean
[thms]: ../../Silmaril/Formats/Compression/Zstd/Huffman/Weights/Thms.lean
[tests]: ../../Silmaril/Formats/Compression/Zstd/Huffman/Weights/Tests.lean
[direct]: ../../Silmaril/Formats/Compression/Zstd/Huffman/DirectWeights/Defs.lean
[table]: ../../Silmaril/Formats/Compression/Zstd/Huffman/SingleStream/Thms.lean
[oracle]: ../../scripts/zstd-huffman-weights-oracle/check.py
[zstd]: https://github.com/facebook/zstd/tree/f8745da6ff1ad1e7bab384bd1f9d742439278e99
