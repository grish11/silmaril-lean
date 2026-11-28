# Brotli distance parameters and literal context modes

`Brotli.ContextHeader.read` starts at `NBLTYPESL` in an identified
compressed meta-block. It reuses the checked block-control parser and
continues from its exact cursor with the unspent portion of the same
bit budget. `readAfter` is the corresponding entry point when the
caller already has the post-control cursor and literal type count.
[RFC 7932 §§3.3, 4, 7.1 and 9.2](https://www.rfc-editor.org/rfc/rfc7932)
· [Block controls](brotli-block-controls.md)

The suffix contains the two-bit `NPOSTFIX`, the four-bit direct
distance field, and one two-bit context mode per literal block type in
type order. The modes are LSB6, MSB6, UTF-8 and signed, in wire code
order. The derived `NDIRECT` is the four-bit field times
`2 ^ NPOSTFIX`. The standard distance alphabet has
`16 + NDIRECT + 48 * 2 ^ NPOSTFIX` entries.

`readAfter_sound` proves the original bits, exactly
`6 + 2 * NBLTYPESL` bits of advancement, the unchanged suffix and the
cap. `read_sound` relates those fields to the exact original control
prefix and its returned cursor. `Wire.length` gives the suffix extent.
`Fields.ranges` proves the distance alphabet is 64–520, `NDIRECT` is
at most 120 and it is divisible by the postfix scale.

Every encoding of these fixed-width fields is assigned by the RFC.
Deterministic tests distinguish an invalid supplied literal count, a
malformed or truncated control prefix, truncation in each of the
post-control fields, and a too-small caller budget. The parser stops
before the literal context map. Context map decompression, context
evaluation, symbol execution and Parquet dispatch are outside the
slice.

## Independent replay

The oracle pins libbrotli 1.2.0 at
`028fb5a23661f123017c060daa546b55cf4bde29`, PyArrow 26.0.1 at
`9e5d6978e9acf372cc989aaaf94e863fe8582c90`, and Thrift 0.25.0 at
`27e8a425ffb498e190df3a12e239326bf5ba9ed6`. A diagnostic native
decoder reports the exact beginning, post-control and post-mode
positions and the decoded fields. It also matches the unmodified
decoder's whole-stream output.

Two PyArrow payloads and two regular CLI streams exercise LSB6,
UTF-8 and signed modes, including multiple literal types. Four streams
from the unmodified encoder API at quality 7 exercise every postfix
value, with direct counts 15, 12, 60 and 120. These four streams use
explicit native encoder parameters. MSB6 is covered by an authored
RFC control in Lean. Every producer fixture checks both entry points,
the exact remainder and rejection with one bit less.
[Fixture manifest](../../scripts/brotli-context-header/fixtures.json)
· [Oracle](../../scripts/brotli-context-header/check.py)

```sh
lake build --wfail +Silmaril.Formats.Compression.Brotli.ContextHeader.Tests
python -m pip install pyarrow==26.0.1 thrift==0.25.0
python -B -I scripts/brotli-context-header/check.py
```

The oracle uses Git, CMake and a C compiler. Pass
`--brotli-source /path/to/brotli` to use a clean checkout at the pin.
