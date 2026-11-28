# Opt-in Parquet codec 4 with raw Brotli meta-blocks

`ScalarPage.BrotliRaw.decodePage` expands the exact body of a flat PLAIN
data page when the supplied column codec is 4. The caller supplies the
framed body and `ScalarPage.Parameters`. `decodePayload` is the narrower
entry point for a slice already selected for Brotli by the caller. The
default `Payload.decode` still reports codec 4 as unsupported.

- V1 hands the whole original body to the raw Brotli decoder.
- V2 checks the raw definition-level span against both size declarations
  before subtracting. The output starts with the unchanged level bytes.
  True and absent `is_compressed` decode the exact value suffix using
  Brotli. False uses the existing exact uncompressed payload path.

`decodePage_sound` relates the original and expanded bodies, including
both declared sizes, page caps and the exact V2 prefix and suffix.
`decodePayload_sound` binds the exact compressed and plain lengths to
the standalone raw stream relation. `decodePayload_streamError` connects
the stream error to the adapter error after the external guards pass.
The Brotli output budget is the declared plain extent. A stream that
exceeds it reports an output size mismatch. A declaration that exceeds
the caller cap reports a caller output limit before decoding.

The [raw Brotli profile](brotli-raw-metablocks.md) admits a standard
window header, non-last raw meta-blocks and an empty terminal
meta-block. Entropy-coded and metadata blocks retain distinct
unsupported errors, and malformed or trailing stream data retains its
Brotli cause. The adapter operates at the expanded-byte boundary.
Framing and CRC validation, level and PLAIN value interpretation,
dictionary pages and selected-column dispatch are separate.
[RFC 7932](https://www.rfc-editor.org/rfc/rfc7932)
· [Pinned Parquet compression](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Compression.md)
· [Pinned Parquet Thrift IDL](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift)

## Independent replay

The [fixture manifest](../../scripts/parquet-brotli-raw/fixtures.json)
identifies original files, codec slices, expanded bodies and modes by
hash or exact extent. PyArrow **26.0.1** at
`9e5d6978e9acf372cc989aaaf94e863fe8582c90` produces the V1 raw-Brotli file
and a V2 file with flag false. Thrift **0.25.0** at
`27e8a425ffb498e190df3a12e239326bf5ba9ed6` extracts their page extents.
The libbrotli **1.2.0** reference at
`028fb5a23661f123017c060daa546b55cf4bde29` independently decodes each
compressed slice. Lean receives the original bytes through the checked
footer and page readers and compares the entire expanded body.

The compressed V2 positives are authored wrappers around the PyArrow
V2 levels and a raw-only libbrotli stream of the value bytes. One has a
true flag and one omits it. PyArrow reads back both whole files. The
pinned PyArrow writer emits compressed V2 values only when compression
shrinks them, while the raw-only stream adds bytes. The native V2
flag-false file is also checked with zero Brotli budget. Two native
entropy payloads and an authored metadata control decode in the native
reference and receive their respective unsupported errors in Lean.
[PyArrow writer condition](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/cpp/src/parquet/column_writer.cc#L1053-L1067)

The replay also checks wrong codec, both size declarations, caller
caps, both sides of the V2 level-span guard, both incorrect flag
directions, truncation, trailing data and the default codec-4 gate.

```sh
lake build --wfail +Silmaril.Formats.Parquet.ScalarPage.BrotliRaw.Thms +Silmaril.Formats.Parquet.FlatColumn.Defs
python -m pip install pyarrow==26.0.1 thrift==0.25.0
python -I scripts/parquet-brotli-raw/check.py
```

The replay builds the pinned reference using Git and CMake. An
existing clean reference checkout can be supplied with
`--brotli-source /path/to/brotli`.
