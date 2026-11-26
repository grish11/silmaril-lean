# Plaintext Parquet footer

This reader takes an immutable `Silmaril.Formats.Bytes` snapshot of a file.
`Silmaril.Formats.Parquet.Footer.Defs` exposes the executable entry points.
`Silmaril.Formats.Parquet.Footer.Thms` exposes the Lean contracts. This is the
plaintext footer slice of the [Arrow and Parquet coverage matrix](arrow-parquet-coverage.md).

## Contract

- `locate` checks the leading and trailing `PAR1`, reads the unsigned four-byte
  little-endian length before the trailer, and returns a nonempty span after
  the leading magic. It checks the available bytes and the footer cap before
  copying the footer. `readFooter` sends only this slice to the Compact reader.
- `readMetadataPrefix` walks one Compact struct and reports the offset after
  its STOP. `readMetadata` requires this offset to equal the slice length.
  The structural pass checks the wire types, field deltas, scalar widths,
  lengths, collection elements and STOPs, including for unknown fields.
  Skipping an unknown binary checks its end offset without copying the bytes.
  Default limits are 8 MiB per footer, 1 MiB per binary, 65,536 elements or
  map entries per collection, 256 fields per struct and 32 open containers.
  Callers can override these and select the permissive varint spelling mode.
  Direct `readMetadata` callers supply their own bounded slice.
- The typed projection contains file version, schema, row groups, counts and
  producer, together with physical types, repetition, column paths, codec
  and encoding IDs, and represented page, index and Bloom locations. It checks
  the required fields and rejects duplicate projected fields, wrong wire types
  and invalid UTF-8 in projected strings. `ColumnChunk.meta_data` is required
  by this profile. Compression and encoding IDs are preserved as integers.
  Optional annotations, sorting, statistics and key/value metadata are skipped
  structurally. Deprecated file offsets are exposed as metadata. Empty column
  file paths are admitted as local, and nonempty paths and encryption markers
  are rejected. The enclosing format is an unencrypted `PAR1` file.
- `validate` separately checks file versions 1 and 2, a bounded depth-first
  schema with unique sibling names, ordered leaf paths and physical types in
  each row group, row counts, and represented data, page index and Bloom
  intervals. It accepts the legacy `REQUIRED` root marker and treats a zero
  leaf child count as absent. Each column chunk starts at its dictionary page
  offset when present or its first data page offset otherwise. It has positive
  length, bounds its data and index page offsets, and ends before or at the
  start of the footer. A Bloom offset
  without a length is checked as a position. Deprecated offsets, row-group
  storage hints, inter-chunk overlap, page contents and logical annotations
  are outside these semantic checks. The span start and the schema depth cap
  are arguments to `validate`.

The wire baseline is `apache-parquet-format-2.14.0` at
`04d56f291ff963e98bc37ab8100e2fc133ff583c`. The `parquet.thrift` SHA-256 is
`d1d9a663d5543789b63d7168179d9849db06958b02c70ba96ba46ffde9278f61`.
Compact follows Apache Thrift v0.25.0 at
`27e8a425ffb498e190df3a12e239326bf5ba9ed6` and reuses the value readers from
[#4201](https://github.com/hiloopai/silmaril-lean/pull/4201). The v0.25.0 Compact
protocol document has SHA-256
`3bb6c620c2fb9404a3b31073281f97a52b99d207d6817c9fddfef4996758824b`.
[File layout][layout] · [Pinned IDL][idl] · [Compact protocol][compact] ·
[Binary protocol extensions][extensions] · [Compact value readers](thrift-compact.md)

## Verified claims

All names below are in `Silmaril.Formats.Parquet.Footer`.

| Theorem | Claim |
| --- | --- |
| `locate_ok_iff` | Success is equivalent to `Framed`, including magic, nonempty placement, advertised width and the caller cap. |
| `framed_slice` | The runtime extraction is the checked byte slice for a framed span. |
| `readMetadata_ok_iff` | The exact reader succeeds precisely when the typed prefix reader finishes at the end of its slice. |
| `readFooter_ok_iff` | File-level success is equivalent to framing and prefix-reader success on the checked slice at the advertised width. |
| `checkDataSpan_some_iff` | Successful interval conversion preserves signed endpoints and gives an ordered in-file span before the footer. |

Typed projection and semantic validation are exercised by regressions. The
claims above concern framing, exact consumption and interval arithmetic.
Page decoding, a writer, encryption, and Arrow events remain outside this slice.
[Theorem header](../../Silmaril/Formats/Parquet/Footer/Thms.lean) ·
[Proofs](../../Silmaril/Proofs/Formats/Parquet/Footer/Contracts.lean)

## Fixture manifest and reproduction

| Input | Provenance |
| --- | --- |
| `alltypes_plain.parquet` | Apache Parquet testing `data/alltypes_plain.parquet` at `0e00127a431f83388d38eebb22cf644d06e86a15`. Exact SHA-256 `12a618d20a59ee0967fef45e7ec1ff6d451e724838edc1bbeac780ca15e8fcc4`. Apache-2.0. Producer `impala version 1.3.0-INTERNAL (build 8a48ddb1eff84592b3fc06bc6f51ec120e1fffc9)` from `created_by`. The corpus does not record the generation command. The footer records `UNCOMPRESSED` and `RLE`, `PLAIN_DICTIONARY`, `PLAIN`. [Upstream fixture][fixture] · [Upstream license][license] · [Local fixture](../../tools/parquet-footer/fixtures/alltypes_plain.parquet) |
| Small synthetic vectors | Explicit byte lists and mutations in the regression module. These cover framing, exact consumption, bounded skipping and malformed or unsupported metadata. [Vectors and native checks](../../tools/parquet-footer/ParquetFooterRegression.lean) |

The pinned fixture is 1,851 bytes, with a 730-byte footer at offset 1,113.
The native suite checks file version 1, eight rows, one row group, eleven
columns, all column paths and physical types, and all data and dictionary page
offsets and compressed sizes. These expectations were cross-checked using
PyArrow 26.0.1 and DuckDB 2.0.1. The regression also checks
semantic rejection of inconsistent schema arity, column paths, row count and
out-of-file offsets. CI checks the fixture SHA-256 and runs the native test
from `make check`. Lake tracks the fixture as an executable input.

```sh
lake build --wfail +Silmaril.Formats.Parquet.Footer.Thms +Silmaril.Formats.ThriftCompact.Examples parquet-footer-regression
.lake/build/bin/parquet-footer-regression
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Footer.Thms +Silmaril.Formats.ThriftCompact.Examples parquet-footer-regression'
sha256sum tools/parquet-footer/fixtures/alltypes_plain.parquet
```

[layout]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/README.md
[idl]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift
[compact]: https://github.com/apache/thrift/blob/27e8a425ffb498e190df3a12e239326bf5ba9ed6/doc/specs/thrift-compact-protocol.md
[extensions]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/BinaryProtocolExtensions.md
[fixture]: https://github.com/apache/parquet-testing/blob/0e00127a431f83388d38eebb22cf644d06e86a15/data/alltypes_plain.parquet
[license]: https://github.com/apache/parquet-testing/blob/0e00127a431f83388d38eebb22cf644d06e86a15/LICENSE.txt
