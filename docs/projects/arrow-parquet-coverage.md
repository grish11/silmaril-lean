# Arrow and Parquet coverage

This matrix records the starting point and the evidence required to claim a
profile of the Arrow or Parquet specification. The baseline is
[Silmaril main at `31fc62d436ad71ebda06e316b4eb54854324ef92`](https://github.com/hiloopai/silmaril-lean/tree/31fc62d436ad71ebda06e316b4eb54854324ef92).
At that revision there is no Arrow Columnar or IPC codec, Parquet file codec,
Hive partition reader, or CSV codec. The abstract relational, byte and
compression APIs below already exist.

**Foundation** means a named interface or theorem exists in Silmaril. It gives
no format-specific coverage. **Open** means the profile's implementation and
evidence have yet to land. **Open, optional** and **open, legacy** mark gaps in
separately scoped profiles. Optionality within a file does not make the behavior
optional once the profile admits that file. The proof and fixture columns state
what future changes must establish.

## Pinned specifications

| Area | Baseline |
| --- | --- |
| Arrow | Columnar format **1.5** and IPC metadata **V5** from Apache Arrow **26.0.1**, commit `9e5d6978e9acf372cc989aaaf94e863fe8582c90`. Keep format, IPC metadata, and producer library version separate. [Columnar and IPC](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst) · [Versioning](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Versioning.rst) · [Schema, Message, File and tensor IDLs](https://github.com/apache/arrow/tree/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format) |
| Arrow metadata wire | FlatBuffers commit `03fffb25e2d777462b719cb4964249c30b19d58f`, tag `v25.12.19-2026-02-06-03fffb2`. [Wire internals](https://github.com/google/flatbuffers/blob/03fffb25e2d777462b719cb4964249c30b19d58f/docs/source/internals.md) |
| Parquet | `apache-parquet-format-2.14.0`, commit `04d56f291ff963e98bc37ab8100e2fc133ff583c`. Track footer version, page version and emitted encodings independently of the spec release. [File and pages](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/README.md) · [Thrift IDL](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift) · [Encodings](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md) · [Logical types](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/LogicalTypes.md) · [Compression](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Compression.md) |
| Parquet metadata wire | Apache Thrift v0.25.0, commit `27e8a425ffb498e190df3a12e239326bf5ba9ed6`. [Compact protocol](https://github.com/apache/thrift/blob/27e8a425ffb498e190df3a12e239326bf5ba9ed6/doc/specs/thrift-compact-protocol.md) · [Parquet protocol extensions](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/BinaryProtocolExtensions.md) |
| Compression wire | Snappy 1.2.2 at `6af9287fbdb913f0794d0148c6aa43b58e63c8e3`, and LZ4 v1.10.0 at `ebb370ca83af193212df4dcbadcc5d87bc0de2f0`. Use the format-specific framing and codec IDs. [Snappy raw](https://github.com/google/snappy/blob/6af9287fbdb913f0794d0148c6aa43b58e63c8e3/format_description.txt) · [LZ4 block and frame](https://github.com/lz4/lz4/tree/ebb370ca83af193212df4dcbadcc5d87bc0de2f0/doc) · [DEFLATE RFC 1951](https://www.rfc-editor.org/rfc/rfc1951) · [Gzip RFC 1952](https://www.rfc-editor.org/rfc/rfc1952) · [Zstd RFC 8878](https://www.rfc-editor.org/rfc/rfc8878) · [Brotli RFC 7932](https://www.rfc-editor.org/rfc/rfc7932) |
| Time and text | ISO 8601-1:2019 including Amd 1:2022 and ISO 8601-2:2019 for extensions. RFC 3339 §5.6–5.7 fixes the first timestamp text profile. RFC 9557 and a pinned tzdb apply when interpreting annotations and named zones. CSV starts at RFC 4180 §2 with explicit dialect and schema policy. [ISO 8601-1](https://www.iso.org/standard/70907.html) · [ISO 8601-2](https://www.iso.org/standard/70908.html) · [RFC 3339](https://www.rfc-editor.org/rfc/rfc3339) · [RFC 9557](https://www.rfc-editor.org/rfc/rfc9557) · [tzdb 2025b](https://github.com/eggert/tz/tree/7e1145bfdb9630c127841dc8ce808a937a300938) · [RFC 4180](https://www.rfc-editor.org/rfc/rfc4180) · [CSVW, 2015](https://www.w3.org/TR/2015/REC-tabular-data-model-20151217/) |
| Dataset and legacy producers | Hive 4.1.0 at `75e40b7537c91a70ccaa31c397d21823c7528eeb`, Arrow 26.0.1, Spark 4.1.0 at `e221b56be7b6d9e48e107fc4d1cf0c15f02700f8`, parquet-java 1.16.0 at `402c3810c372d29603e181771acebfecc71bef61`. These fix particular interoperability behaviors, including path parsing and INT96. [Hive path escaping](https://github.com/apache/hive/blob/75e40b7537c91a70ccaa31c397d21823c7528eeb/common/src/java/org/apache/hadoop/hive/common/FileUtils.java) · [Arrow partition API](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/cpp/src/arrow/dataset/partition.h) · [Spark partitions](https://github.com/apache/spark/blob/e221b56be7b6d9e48e107fc4d1cf0c15f02700f8/sql/core/src/main/scala/org/apache/spark/sql/execution/datasources/PartitioningUtils.scala) · [Spark Parquet writes](https://github.com/apache/spark/blob/e221b56be7b6d9e48e107fc4d1cf0c15f02700f8/sql/core/src/main/scala/org/apache/spark/sql/execution/datasources/parquet/ParquetWriteSupport.scala) · [parquet-java NanoTime](https://github.com/apache/parquet-java/blob/402c3810c372d29603e181771acebfecc71bef61/parquet-column/src/main/java/org/apache/parquet/example/data/simple/NanoTime.java) |

## Existing foundations

| Interface | Foundation at the baseline |
| --- | --- |
| Abstract table | `Row` is a column-indexed dependent function and `Table` an ordered list of rows. `AlignedColumns` carries an explicit row count, including at zero columns. `AlignedColumns.rowsEquiv` relates the two. `ColumnMap.pullRow` projects by a typed column map. [Table definitions](../../Silmaril/Semantics/Relational/Table/Organization/Defs.lean) · [Schema definitions](../../Silmaril/Semantics/Relational/Table/Schema/Defs.lean) · [Table theorems](../../Silmaril/Semantics/Relational/Table/Thms.lean) |
| Abstract database | `Database.Packed` is a partial name map to dependent schema/table pairs. `Dependent` presents the same data as catalog and payloads. `dependentEquivPacked`, `Packed.erase`, `Recoverable` and `Enumeration` support conversion, erasure and finite export. Executable import needs an explicit algorithm for the chosen representation. [Database definitions](../../Silmaril/Semantics/Relational/Database/Defs.lean) · [Database theorems](../../Silmaril/Semantics/Relational/Database/Thms.lean) |
| Query observations | `QueryRel.Refines`, `AgreesOn` and `observe` select the result relation. `ResultRows` distinguishes ordered, bag and membership observations. `StreamStep`, `StreamPrefix` and `StreamDrains` track yields and terminal errors. `TableQuery.institution` and `DatabaseQuery.institution` cover Boolean row-existence queries with schema reindexing. `ITree.Signature` gives typed request/reply. [Query definitions](../../Silmaril/Semantics/Relational/Query/Defs.lean) · [Results](../../Silmaril/Semantics/Relational/Query/Result.lean) · [Query institutions](../../Silmaril/Logic/RelationalQuery/Thms.lean) · [Interaction signatures](../../Silmaril/Semantics/ITree/Signature/Defs.lean) |
| SQLite | `SqlValue` models storage classes. `PackedDatabase`, `PackedColumnDatabase` and `Snapshot` model typed tables and catalog data. `CatalogExecutor.executor_sound` and `executor_complete` cover the checked read profile. `Bridge.execute_corresponds` connects its bound calls to the storage model. [Values](../../Silmaril/Semantics/SQLite/Relational/Value/Defs.lean) · [Catalog](../../Silmaril/Semantics/SQLite/Relational/Catalog/Defs.lean) · [Executor laws](../../Silmaril/Semantics/SQLite/Relational/Executor/Catalog/Thms.lean) · [Storage bridge](../../Silmaril/Machine/SQLite/Relational/Bridge/Thms.lean) |
| Bytes, text and time | `KBytes.readLE` and checked slice laws provide byte views. `ByteFormat.Parses` and `ByteFormat.Paired` support specification and kernel/native checkers. `ByteStreams` supplies byte chunk acceptance lemmas. `Formats.Category.Format.records` accepts a caller-supplied framing function. Existing ASN.1 time and exact decimal text work provide precedents for narrower profiles. `Parse.ByteParse` currently brings Wasm imports and is outside the Formats region's permitted dependencies. [Byte views](../../Silmaril/Prelude/Bytes/Thms.lean) · [ByteFormat](../../Silmaril/Prelude/Bytes/Format/Defs.lean) · [Byte streams](../../Silmaril/Formats/ByteStreams/Thms.lean) · [Record framing](../../Silmaril/Formats/Category/Defs.lean) · [ASN.1 time](../../Silmaril/Formats/ASN1/Time/Thms.lean) · [Decimal text](../../Silmaril/Numeric/DecimalText.lean) · [Regions](../../regions.toml) |
| Compression and checksums | `Compression.Format` provides parameterized decoders and capabilities. `Gzip.decoder`/`encoder` and `Gzip.roundTrip` cover the member contract. `DeflateSpec.deflateTake_iff` relates the DEFLATE decoder to its stream relation. `Checksum.crc32` supplies the page checksum primitive. `Zstd.frame`/`decode` cover raw/RLE blocks, with general compressed blocks open. Parquet page and Arrow buffer composition, including budgets and framing, remain open for all codecs. [Format](../../Silmaril/Formats/Compression/Format/Defs.lean) · [Catalogue](../../Silmaril/Formats/Compression/Catalog/Thms.lean) · [Gzip](../../Silmaril/Formats/Compression/Gzip/Thms.lean) · [DEFLATE](../../Silmaril/Formats/Compression/DeflateSpec/Thms.lean) · [CRC-32](../../Silmaril/Formats/Compression/Checksum/Thms.lean) · [Zstd](../../Silmaril/Formats/Compression/Zstd/Defs.lean) |

## Format coverage matrix

### Arrow Columnar and IPC

| Component | Initial status | Contract and proof to close | Fixtures and checks |
| --- | --- | --- | --- |
| Primitive physical arrays and batches | Open | Start with nullable Int32 and UTF-8. Prove buffer and validity length, nullability, offset bounds, UTF-8 and batch row alignment. Add Null, bit-packed Boolean, signed/unsigned widths, float bit patterns, decimals, binary, large offsets, fixed-size binary and temporal/interval types. Prove denotation and encode/decode on the admitted types, including sliced arrays. | Empty, all-null and mixed-validity arrays, omitted validity where permitted, invalid bitmaps and offsets, empty strings, IEEE bit-pattern cases and empty batches. |
| Nested and specialized layouts | Open | Cover list, large/fixed-size lists, struct, map, dense/sparse union and dictionary. Follow with run-end encoding, list/binary views and variadic buffers. Prove child ranges, dictionary index bounds and type-specific validity, including null versus empty and behavior of slices. | Nested null and empty combinations, union type IDs and offsets, dictionary encodings of the same values, overlapping valid views and malformed run ends. |
| FlatBuffers and V5 stream | Open | Validate root, vtables, scalars/defaults, vectors, strings, union tags, offsets and features. Enforce Schema-first, continuation marker, lengths/padding, Arrow body endianness, descriptor bounds and legal end. Prove exact message slicing and stream equivalence under re-chunking. | Generated little-endian two-column streams, every split point of small inputs, truncation at metadata/body boundaries, bad vtables and unsupported tag/feature tests. Read and write against PyArrow. |
| IPC file and dictionaries | Open | Check leading/trailing `ARROW1`, footer and block locations; prove indexed reads agree with materialization. Admit dictionary ID, delta and replacement rules separately for streams and files. | File/stream tables with equal denotation, dictionary delta and replacement cases, mismatched schema/blocks, bad footer and malformed dictionary references. |
| IPC buffer compression | Open, optional | Cover LZ4 **frame** and Zstd per buffer. Prove size-prefix and uncompressed-sentinel semantics, exact frame consumption and bounded output. | Per-codec compressed/uncompressed mixtures, unsupported Zstd cases for the initial subset, wrong size and truncated frame. |
| Compatibility and other messages/interfaces | Open, legacy and optional | Give early IPC framing and V4 layouts a reader profile. Track still older metadata versions and big-endian inputs explicitly. Track extension metadata/type interpretations, tensors, sparse tensors, C Data and C Stream as separate claims. C interfaces need ownership and release contracts at the FFI boundary. | Pinned legacy and big-endian integration fixtures. Test extension metadata retention, tensor shape/stride, C schema/batch lifetime, end-of-stream, error and release per admitted profile. |

### Parquet file, metadata, pages and encodings

| Component | Initial status | Contract and proof to close | Fixtures and checks |
| --- | --- | --- | --- |
| Plaintext footer and Compact wire | Open | Check `PAR1`, little-endian footer length and exact in-file footer consumption. Model field deltas, ZigZag, signed lengths, field/collection types, booleans, stop and bounded skipping of unknown fields. Validate required metadata, schema tree, row groups, column paths and advertised intervals. Give writer and parser separate validity claims. | Narrow generated file, upstream `alltypes_plain.parquet` for a compatible metadata profile, compact vectors, missing fields, invalid footer length and out-of-file offsets. |
| Page framing and checksums | Open | Cover dictionary pages, Data Page V1 and V2, row/value counts and page bounds. V1 can compress the whole payload. V2 has uncompressed level spans and separately governed value compression. Prove exact level/value slices and consumption. Check CRC-32 over serialized page data when present. | Uncompressed tiny pages, V1/V2 Snappy, empty pages, invalid header counts, truncated payloads and the corrupt-checksum case. |
| Levels, physical values and nested schema | Open | Start with flat optional INT32, PLAIN and hybrid RLE/bit-packed levels. Cover every physical type, sibling alignment, repetition across page boundaries, and null/empty nested distinctions. Prove Dremel reconstruction and profile writer round-trip. | Required/optional/repeated fields, multiple page boundaries, empty and null lists/maps, nested structs, cross-leaf count mismatch and invalid levels. |
| Value encodings | Open | Cover PLAIN, RLE, RLE_DICTIONARY, DELTA_BINARY_PACKED, DELTA_LENGTH_BYTE_ARRAY, DELTA_BYTE_ARRAY, BYTE_STREAM_SPLIT and ALP, restricted by the encoding/type matrix. Track deprecated PLAIN_DICTIONARY and BIT_PACKED as legacy readers. Prove bit order, run/delta/width arithmetic, padding, lookup bounds and denotation. | Hand vectors plus independent producers. Exercise zero bit width, truncated runs, padding, bad dictionary indices, signed extremes, floating-point edge cases and the permitted encoding/type combinations. |
| Logical types and old schema conventions | Open, includes legacy | Check physical/logical associations, sort rules, signed/unsigned, string/binary, decimal, date, time and interval. Include remaining annotations, such as UUID and FLOAT16, and track Variant, geospatial and FILE under explicit feature profiles. Apply ConvertedType and legacy LIST/MAP rules, with the timestamp cases below. | Round trips for representable values, illegal type/width/scale combinations, old/current nested schemas and typed fixtures for each admitted annotation. |
| Page compression | Open, includes legacy | Admit UNCOMPRESSED first, then raw Snappy, GZIP, LZ4_RAW, Zstd, Brotli, and pinned legacy LZO and Parquet LZ4 profiles. Validate compressed and expanded lengths, exact input consumption and budget before allocation. Bind each codec to the page's framing. | Independent codec vectors, limits and corrupt frames, V1/V2 boundary tests, raw/Hadoop LZ4 fixtures and ordinary compressed Zstd blocks. |
| Metadata-driven access and encryption | Open, optional | Cover statistics and sort order, page/offset index and split-block Bloom filters. Prove pruning sound with nulls, NaNs and missing/invalid evidence. Validate external references against the source snapshot. Track plaintext/encrypted footer and encrypted-column modes with distinct authentication and trust contracts. | Pruned and unpruned results, malformed/stale metadata and unsupported fields, sidecar/external offset errors, and encryption vectors with a pinned producer and tampering tests. [Page index](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/PageIndex.md) · [Bloom filter](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/BloomFilter.md) · [Encryption](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encryption.md) |

### Tables, time and interoperability

| Component | Initial status | Contract and proof to close | Fixtures and checks |
| --- | --- | --- | --- |
| Tables, events and filtering | Foundation for tables and query observations. Format bridge open. | Denote checked batches as typed rows with explicit row count, field positions/IDs, metadata and nulls. Prove projection and stable filtering with explicit three-valued logic, null-mask policy and predicate-field premises. Relate API open/next/close/error to Arrow schema/dictionary/batch/end events. Prove prefix and drain equivalence under re-batching at the selected row/error observation. Pruning with visible decode errors needs validation or a stated error policy. | Zero-column tables, duplicate values/names, null/empty cells, chunk boundaries, cancellation and a good prefix followed by error. Compare supported Arrow masks against the reference filter. |
| Text time and fixed-point ticks | Foundation for restricted text/decimal helpers. Timestamp profile open. | Distinguish instant, local civil time and preserved annotation. Parse/print an RFC 3339 subset first, with exact fractions and explicit `-00:00` and leap-second policy. Add selected ISO calendar, ordinal/week, expanded-year and precision forms by edition. Interpret signed ticks by epoch and scale. Prove representability iff divisible and in range, exact inverses, and signed residual bounds for named rounding modes. Apply a pinned tzdb for gaps and folds. | Negative fractions, pre-epoch ticks, offset/day rollover, invalid dates, >9 fractional digits, overflow, both Int64 endpoints, tie rounding and ambiguous wall time. |
| Arrow/Parquet time and legacy | Open, includes legacy | Arrow provides Int64 seconds/millis/micros/nanos and optional timezone. A nonempty timezone supplies an instant interpretation with a UTC epoch and a zone annotation. An empty timezone supplies local coordinates. Parquet INT64 `TIMESTAMP` has millis/micros/nanos and an explicit `isAdjustedToUTC` flag. Prove mappings with local 86,400-second days, exact rescaling and explicit annotation/precision loss. Apply ConvertedType rules to legacy-only and paired modern tags. Enable INT96 Julian-day and nanoseconds-of-day decoding only in pinned writer profiles with epoch/rebase/zone policy. | PyArrow/Parquet Java signed ticks, empty versus UTC timezone, annotation loss, invalid tag combinations, INT96 Spark and pre-Gregorian-rebase examples. |
| Parquet to Arrow streaming | Open | Specify an immutable size and bounded `readAt`, with a capped spool profile for forward-only input. Read footer before planning projection. Track pages, dictionaries/levels and pending row state. Prove bounded live data, ordered filtered/projection output and prefix/error/drain refinement, including partial output and backpressure. | Multiple row groups, staggered chunk/page boundaries, nested rows, selected vs skipped columns, short reads, exhaustion and errors after output. Compare drained rows against pinned independent readers. |
| Hive and adjacent layouts | Open at baseline. The [relative directory profile](hive-partition-path.md) now has a checked lexical codec and PyArrow/Hive fixtures. | Parse relative `key=value` paths separately from filesystem discovery. Pin decoding, casing, duplicate/missing/unknown fields, null sentinel and schema/coercion behavior. Distinguish positional directories, filename partitions and unpartitioned scans. Prove reversible path subset, constant-column insertion and sound pruning. Track `_metadata` and `_common_metadata` as explicit planning inputs. Bucketing and table-format manifests/snapshots require their own profiles. | Escaped separators/Unicode, empty/sentinel collisions, in-file column collisions, order, mixed fragments and discovery differences with the selected Hive, Arrow and Spark profiles. |
| Lean DB and CSV | Foundation for abstract DB and SQLite. Format conversions and CSV open. | Export from an explicit table name and row order. Check destination schema/constraints on import. Provide exact rejection and a policy mode with stated erasures, including annotations, width/scale, nested values, identities and catalog constraints. Specify RFC 4180 byte framing, quoting, newline/header/width policy and typed cell conversion. Keep null, empty string and missing field distinct under the chosen dialect. Prove lexical round-trip and typed inverse or correctness modulo declared loss. Bind any schema sidecar to its payload. | Quoted fields with embedded CRLF and escaped quotes, invalid UTF-8, duplicate names, null/sentinel/empty collisions, decimal/timestamp boundaries and DB row order. Compare RFC 4180 cases against a pinned independent parser with the same dialect. |

## Phases and closure conditions

1. **Independent first profiles.** Specify a pure scan and filter over the
   existing relational tables. Establish civil/instant and tick conversion
   laws independently of either format. Build a bounded Arrow V5 vertical
   slice from IPC bytes through nullable Int32 and UTF-8 batches to typed
   rows, with a writer and PyArrow checks in both directions. Build a
   plaintext Parquet footer reader that checks the exact Compact slice and
   exposes typed metadata. The four profiles can be reviewed independently.
   Start under `Semantics/Relational/Scan`, `Numeric` and `Formats/Time`,
   `Formats/Arrow` and `Formats/FlatBuffers`, and `Formats/Parquet/Footer`
   and `Formats/Thrift/Compact`, respectively.
2. **Flat interoperability.** Add Parquet PLAIN and hybrid levels for a flat
   nullable primitive profile, then add Snappy and page variants. A
   Parquet-to-Arrow scan closes this phase when its emitted batches denote
   the same ordered projection and filter as full materialization under the
   same profile. Include a resource bound and prove how errors relate to
   already emitted rows. Add timestamp adapters and exact DB/CSV conversion
   on their representable domains once the corresponding core laws exist.
3. **Broader format and dataset profiles.** Extend buffer, page, nesting,
   dictionary, timestamp and encoding coverage row by row. Require
   successful round-trips with the declared observation and treat byte
   equality as a separate claim for canonical writers. Close the Hive or
   adjacent dataset profile when path policy, typed constants and pruning
   proofs agree with the pinned implementations and validated snapshots.
4. **Compatibility and optional profiles.** Close each legacy or optional
   row independently. Name the exact reader and writer support, expected
   outcomes for unrecognized features, resource limits and any trust or I/O
   assumptions. A profile is closed when every row it admits links to its
   specification, functions, Lean results and fixture runs. Broader claims
   require extending that set of rows.

For each admitted profile, state the wire relation over bytes and the
observable values independently of the implementation. A reader needs
soundness, completeness on its admitted bounded domain, and precise
consumption. A writer needs validity and decode-after-encode at the selected
observation. Include negative tests for malformed, unsupported, limit and I/O
outcomes. Record the theorem names and dependencies. Follow the repository's
public header and proof layout, and keep the runtime closure on definitions.
A differential check establishes agreement on its fixtures. The Lean
theorems carry the general claims. [Contribution rules](../../AGENTS.md) ·
[Axiom policy](../../policy.toml)

## Fixture and build evidence

Pin corpus sources and selected bytes in a fixture manifest. Record the
fixture path or generation command, SHA-256, license, producer version,
options, expected observation and applicable profile. Check independent
writer → Silmaril reader and Silmaril writer → independent reader where a
writer is claimed. Compare ordered rows, nulls, typed metadata and exact
timestamp ticks. Use a pinned PyArrow 26.0.1 build and an independent Parquet
implementation such as parquet-java 1.16.0 or DuckDB 2.0.1
(`8d78114e90a53823803660bf821f6073ac87da8c`).
[Arrow release](https://github.com/apache/arrow/releases/tag/apache-arrow-26.0.1) ·
[parquet-java pin](https://github.com/apache/parquet-java/tree/402c3810c372d29603e181771acebfecc71bef61) ·
[DuckDB pin](https://github.com/duckdb/duckdb/tree/8d78114e90a53823803660bf821f6073ac87da8c)

These public fixtures provide immutable inputs for the indicated checks. Use
smaller generated fixtures for the initial IPC schema and Parquet page
profiles. The hashes identify the inputs. The expected framing observations
do not establish reader, writer or theorem coverage.

| Pinned input | SHA-256 | Expected check |
| --- | --- | --- |
| [Arrow primitive file][arrow-file] | `7aab19247177ea959506d7b192e8e21235f082267c72f394bb788c615ce03f54` | `ARROW1` at both ends, 2,000-byte footer at 20,288. |
| [Arrow primitive stream][arrow-stream] | `ea7546616d90c9de86d9c8045d53a6ec647070121f695971d0da830a2ebac19e` | Continuation marker, 1,928-byte first metadata span and explicit EOS. |
| [Arrow primitive reference JSON][arrow-json] | `ff3aebe4380cb9f22da7e5a7356d0c0ba4ba4567a5ee94a55876701cd70d58af` | 30 fields, with 17 and 20 rows in the two batches. |
| [Parquet alltypes_plain.parquet][parquet-plain] | `12a618d20a59ee0967fef45e7ec1ff6d451e724838edc1bbeac780ca15e8fcc4` | `PAR1` at both ends, 730-byte footer at 1,113. |

Select later fixtures from the [Arrow integration corpus][arrow-corpus] at
`5a26d35785ff8761e56d79eebff971f6f737e18c` (legacy, big-endian, dictionary,
datetime and nested) and the [Parquet corpus][parquet-corpus] at
`0e00127a431f83388d38eebb22cf644d06e86a15` (including
`datapage_v2.snappy.parquet`, `datapage_v1-corrupt-checksum.parquet`,
`int96_from_spark.parquet` and `lz4_raw_compressed.parquet`).

When implementation lands, build the touched theorem roots and runtime
targets with `lake build --wfail`. Execute the fixture checks separately,
including small kernel-checked vectors and the native interoperability
suite. Register the targets and fixtures for `make check` and verify that
CI selects them on implementation and fixture-only changes. Run unscoped
`make check` on the integrated main baseline. Record the checked commit,
profile, toolchain, targets and results with the claims they support.
[Development setup](../development.md) · [Build targets](../../Makefile) ·
[CI path filters](../../.github/paths-filter.yml)

[arrow-corpus]: https://github.com/apache/arrow-testing/tree/5a26d35785ff8761e56d79eebff971f6f737e18c/data/arrow-ipc-stream/integration
[arrow-file]: https://github.com/apache/arrow-testing/blob/5a26d35785ff8761e56d79eebff971f6f737e18c/data/arrow-ipc-stream/integration/1.0.0-littleendian/generated_primitive.arrow_file
[arrow-stream]: https://github.com/apache/arrow-testing/blob/5a26d35785ff8761e56d79eebff971f6f737e18c/data/arrow-ipc-stream/integration/1.0.0-littleendian/generated_primitive.stream
[arrow-json]: https://github.com/apache/arrow-testing/blob/5a26d35785ff8761e56d79eebff971f6f737e18c/data/arrow-ipc-stream/integration/1.0.0-littleendian/generated_primitive.json.gz
[parquet-corpus]: https://github.com/apache/parquet-testing/tree/0e00127a431f83388d38eebb22cf644d06e86a15/data
[parquet-plain]: https://github.com/apache/parquet-testing/blob/0e00127a431f83388d38eebb22cf644d06e86a15/data/alltypes_plain.parquet
