# Plaintext Parquet page framing

`Silmaril.Formats.Parquet.Page.Defs` reads a bounded plaintext column chunk
from a finite file snapshot. It reuses the [footer reader](parquet-footer.md)
for the column metadata and the [Thrift Compact readers](thrift-compact.md)
for wire decoding. The IDL is Parquet format **2.14.0** at
`04d56f291ff963e98bc37ab8100e2fc133ff583c`. The SHA-256 of the pinned
`parquet.thrift` is `d1d9a663d5543789b63d7168179d9849db06958b02c70ba96ba46ffde9278f61`.
The Compact baseline is Apache Thrift **0.25.0** at
`27e8a425ffb498e190df3a12e239326bf5ba9ed6`.
[Pinned IDL][idl] · [Page layout][layout] · [Compact wire format][compact]

## Reader profile

- `columnSpan` applies the footer's checked signed interval conversion to the
  dictionary-page offset when present, or the data-page offset otherwise,
  and `total_compressed_size`. The caller supplies the footer start from the
  same snapshot. Explicit chunk spans may also be supplied. `readPage` checks
  the absolute cursor and chunk end against the snapshot and limits its
  Compact lookahead to the lesser of the chunk end and the caller's header
  cap. The default cap is 64 KiB per header. A header cut by that window
  reports a Compact truncation error.
- `readHeaderPrefix` indexes one `PageHeader` through its Compact STOP,
  then projects typed fields using only those consumed bytes. The projection
  checks required fields, duplicates among projected fields, wire types,
  nonnegative sizes and counts, and the match between kind and its detail
  field. It retains encoding IDs and the optional 32-bit CRC bits. Data Page
  V2 defaults `is_compressed` to true, checks counts and both advertised
  lengths, and requires equal compressed and uncompressed size when the
  flag is false. Statistics and unrecognized fields are traversed with the
  Compact bounds and discarded.
- `readChunk` scans through the exact chunk end or returns an error. The
  default is at most 65,536 pages. Each page records its absolute half-open
  header and on-disk payload spans. `Frame.v2Spans` gives repetition,
  definition, and value spans in that order. Empty payloads and empty V2
  sections use zero-width spans. The reader allocates a bounded header
  window and a frame list. Payload bytes are represented by offsets.
- The typed kinds are Data Page V1, Data Page V2, and dictionary. `INDEX_PAGE`
  with its matching struct is framed as `skipped indexPage`. An unrecognized
  kind with no known detail field is framed as `skipped (unknown code)`.
  A skipped frame advances past its checked payload and gives no page
  content interpretation. The caller can reject these kinds by inspecting
  the result.

This profile covers plaintext in-file chunks from the footer. Header and
framing contracts are independent of physical types and codecs. The fixture
containing INT96 exercises its page layout only. Dictionary placement,
counts across pages, row-boundary checks, statistics, page indexes, CRC
validation, encrypted chunks, and external column files are outside the
profile. The corrupt-checksum fixture `datapage_v1-corrupt-checksum.parquet`
is reserved for checksum verification. `int96_from_spark.parquet` and
`lz4_raw_compressed.parquet` are outside the fixture set. Page payload
decompression, level decoding, and scalar decoding use separate interfaces.
[Coverage matrix](arrow-parquet-coverage.md) · [Payload decompression](parquet-page-payload.md)

## Lean contracts

The page theorems are in `Silmaril.Formats.Parquet.Page`.

| Theorem | Claim |
| --- | --- |
| `readHeaderPrefix_stop` | The consumed prefix is nonempty and ends immediately after an in-window STOP. |
| `readPage_exactPrefix` | The checked source slice at the cursor is exactly the consumed length, ends at that STOP, and stays under the header cap. |
| `readPage_within` | The header advances the cursor. Its adjacent payload has the advertised compressed length and ends inside the chunk and source. |
| `readChunk_chain` | The frames form a contiguous chain from the chunk start to its exact end. |
| `readChunk_payloads_bounded` | Every payload in the chain lies inside the declared chunk. |
| `readChunk_payloads_disjoint` | Every earlier payload ends at or before every later header starts. |
| `v2Spans_bounds` | A returned V2 split partitions the on-disk payload with ordered, adjacent spans. |

The prefix proof uses `Silmaril.Formats.ThriftCompact.Traversal.readStruct_stop`.
Typed field values and error cases are exercised by the native regression
and the independent fixture comparison. [Page theorem header](../../Silmaril/Formats/Parquet/Page/Thms.lean) · [Compact theorem header](../../Silmaril/Formats/ThriftCompact/Traversal/Thms.lean)

## Pinned fixtures

Both files are from Apache Parquet Testing at
`0e00127a431f83388d38eebb22cf644d06e86a15`, under Apache-2.0. The producer
strings are from their footers. The corpus supplies the file bytes.
[Corpus][fixtures] · [License](../../tools/parquet-footer/fixtures/LICENSE.txt)

| File | SHA-256 | Observation |
| --- | --- | --- |
| [`alltypes_plain.parquet`][plain] | `12a618d20a59ee0967fef45e7ec1ff6d451e724838edc1bbeac780ca15e8fcc4` | Impala `1.3.0-INTERNAL` (build `8a48ddb1eff84592b3fc06bc6f51ec120e1fffc9`), 11 chunks with 21 uncompressed V1 and dictionary pages. |
| [`datapage_v2.snappy.parquet`][v2] | `44f29191b5fa8cfe0ab848495bd8ef89344ac0d8f87b3dff12e267631e2b5c03` | parquet-mr `1.8.1` (build `4aba4dae7bb0d4edbcf7923ae1339f28fd3f7fcf`), 5 chunks with 8 V2 and dictionary pages, including a nested column with both level sections. |

PyArrow **26.0.1** provided the fixture column-chunk locations and Apache
Thrift's Python **0.25.0** implementation independently decoded the page
headers at those locations. The Lean observations agree for all 29 page
boundaries and represented header fields. The native fixture test checks
all offsets and representative typed headers. It also checks wrong and
missing fields, negative lengths, invalid V2 counts and lengths, cut
headers and payloads, bounds, page limits, and skipped kinds.
[Native regressions](../../tools/parquet-page/ParquetPageRegression.lean)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Page.Thms parquet-page-regression
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Page.Thms +Silmaril.Formats.Parquet.Footer.Thms +Silmaril.Formats.ThriftCompact.Examples parquet-page-regression parquet-footer-regression'
```

[idl]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift
[layout]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/README.md
[compact]: https://github.com/apache/thrift/blob/27e8a425ffb498e190df3a12e239326bf5ba9ed6/doc/specs/thrift-compact-protocol.md
[fixtures]: https://github.com/apache/parquet-testing/tree/0e00127a431f83388d38eebb22cf644d06e86a15/data
[plain]: https://github.com/apache/parquet-testing/blob/0e00127a431f83388d38eebb22cf644d06e86a15/data/alltypes_plain.parquet
[v2]: https://github.com/apache/parquet-testing/blob/0e00127a431f83388d38eebb22cf644d06e86a15/data/datapage_v2.snappy.parquet
