# Bounded Brotli raw meta-block streams

`Compression.Brotli.decode` reads one exact stream in the raw meta-block
profile of RFC 7932. Its inputs are a byte list and caller limits for
compressed bytes, output bytes, window size and meta-block steps.
It exposes typed malformed, unsupported and limit failures.
[RFC 7932 §§9.1–9.3][rfc] · [Public definitions][defs]

The window prefix is one of the RFC codes for `WBITS` 10–24. The window
limit compares with `2^WBITS - 16` bytes. The reserved code `0010001`
is rejected. The decoder then accepts zero or more non-last, raw
meta-blocks. A raw block carries a canonical 4-, 5- or 6-nibble
`MLEN - 1` and the uncompressed flag. Its output is exactly the
following `MLEN` bytes after checked zero fill to the next byte boundary.
The output budget is debited before copying each body.

An empty last meta-block, with `ISLAST` and `ISLASTEMPTY` set, terminates
the profile. It consumes the remaining zero fill of that byte and
requires the end of the supplied input. The step budget includes that
terminator. A data-bearing entropy block or a metadata meta-block is
rejected when identified. The reserved metadata bit and noncanonical
raw lengths have their own errors. The bounds describe logical byte
counts and steps. Parquet codec 4 remains a separate integration.

`decode_sound` ties the actual input bits to the window code and the
raw-block wire chain, proves ordered concatenation of exact body bytes,
and gives the input, output, window and step bounds. `bodyStart_aligned`
proves the byte boundary after each header and its zero fill.
`WindowWire.range` and `BlocksWire.stepCount` identify the declared
window range and the step count including the terminator. The shared
`LSBReader.readBits_sound` relates each read to the exact bit prefix and
cursor advance. [Theorem header][thms] · [Bit reader contract][bits]

## Independent differential

The oracle builds libbrotli v1.2.0 at
`028fb5a23661f123017c060daa546b55cf4bde29`. It verifies the entire
output byte sequence for native empty, one-byte and two-block streams,
hand-authored canonical length transitions and a seven-bit window code.
PyArrow 26.0.1 independently writes a real codec-4 PLAIN INT32 V1 file.
Thrift 0.25.0 checks the numeric footer codec and exact original payload
extent. The standalone decoder receives that extracted stream and its
output is checked against both libbrotli and the producer's physical
values. [Manifest][fixture] · [Producer and oracle][oracle] · [Native pin][native]

The rejection suite covers unavailable entropy and metadata modes,
reserved codes, truncation, noncanonical length, nonzero raw and final
fill, trailing bytes and individually exceeded caps. The differential
compares the RFC-invalid controls with native rejection and verifies
that Lean publishes no partial output.

```sh
lake build --wfail +Silmaril.Formats.Compression.Brotli.Tests
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
python3 -m venv /tmp/brotli-raw-oracle
/tmp/brotli-raw-oracle/bin/python -m pip install 'pyarrow==26.0.1' 'thrift==0.25.0'
/tmp/brotli-raw-oracle/bin/python -I scripts/brotli-raw-oracle/check.py
```

[rfc]: https://www.rfc-editor.org/rfc/rfc7932.html#section-9
[defs]: ../../Silmaril/Formats/Compression/Brotli/Defs.lean
[thms]: ../../Silmaril/Formats/Compression/Brotli/Thms.lean
[bits]: ../../Silmaril/Formats/Compression/Bits/Thms.lean
[fixture]: ../../scripts/brotli-raw-oracle/fixtures.json
[oracle]: ../../scripts/brotli-raw-oracle/check.py
[native]: https://github.com/google/brotli/tree/028fb5a23661f123017c060daa546b55cf4bde29
