# Bounded Parquet dictionary chunks

`Silmaril.Formats.Parquet.DictionaryChunk.Defs` reads one local, flat,
uncompressed INT32 column chunk. Give `read` or `scanColumn` the original
snapshot bytes and footer start, the matching `FlatScan.Field` from the
footer schema, the declared row count, and that group's column metadata.
`read` produces a checked chunk plan with typed dictionary entries and
absolute data-page spans. `scanColumn` returns nullable cells in wire order.
This entry point can also read an all-PLAIN chunk.

The implementation uses Parquet Format **2.14.0**, commit
`04d56f291ff963e98bc37ab8100e2fc133ff583c`. The pinned `parquet.thrift`
SHA-256 is `d1d9a663d5543789b63d7168179d9849db06958b02c70ba96ba46ffde9278f61`.
[Coverage matrix][matrix] · [IDL][idl] · [Dictionary wire rules][dictionary]

## Admission and dispatch

- The column path, physical type, codec and slot count must match the
  checked field and row group. The caller establishes the footer, schema
  and group association using the same immutable bytes.
- `Page.columnSpan` and `Page.readChunk` establish a bounded frame chain.
  The optional dictionary is the first frame and its header starts at the
  declared dictionary offset. At least one data frame follows. Its first
  header starts at `data_page_offset`. Duplicate, misplaced, missing or
  undeclared dictionaries, CRC-bearing pages, and skipped page kinds fail.
- The dictionary header admits PLAIN (`0`) and parquet-java's legacy
  PLAIN_DICTIONARY (`2`) label. In both cases `Plain.decodeInt32` consumes
  the exact body as the declared count of little-endian words, under
  separate byte and entry limits. Entries retain wire order. `is_sorted`
  has no role in selecting entries. The dictionary lasts for one chunk.
- V1 and V2 data pages admit PLAIN (`0`), deprecated PLAIN_DICTIONARY (`2`)
  and RLE_DICTIONARY (`8`). A dictionary-coded data page requires the
  leading dictionary. PLAIN remains valid after a dictionary page and uses
  `ScalarPage.decode .int32`. Index-coded pages use `DictionaryIndex.decode`
  with the typed entries and the exact on-disk body. The existing decoders
  own level/index consumption, index bounds, and nullable slot reconstruction.
  V1's deprecated BIT_PACKED tag is accepted only when its maximum level
  is zero and that level section is absent. The chunk adapter maps that
  empty section to the scalar decoder's RLE header convention.
- The plan bounds rows, frames, header lookahead, dictionary bytes and
  entries, and page widths. The scalar and index decoders enforce their
  own level, value and byte caps. Only the data pages contribute row slots.
  Concatenation retains page and slot order and verifies the final row
  count. Required fields exclude null slots.

The profile excludes compression, nested and repeated leaves, non-INT32
physical types, other encodings, and index pages. Admission uses encoding
IDs in the page headers. The footer encoding list and page statistics are
advisory in this profile. File validation, cross-column assembly, and
checksum verification use separate APIs.
[Page framing][framing] · [Dictionary index decoder][indices]

## Lean contracts

| Theorem | Claim |
| --- | --- |
| `read_admitted` | The original frame chain is the optional standalone dictionary followed by admitted data frames. It ties the offsets to footer metadata, the typed dictionary to its exact PLAIN body, and data page admission to layout, byte caps and dictionary presence. |
| `read_payloads` | Each frame's body lies within the chunk and has exactly the advertised compressed length. |
| `scanColumn_ordered` | Slots concatenate matching decoder results in frame order, with the same typed dictionary for all index-coded pages. The length equals the row count, and required slots are present. |

[Theorem header][thms]

## Independent whole-file fixtures

PyArrow **26.0.1** at `9e5d6978e9acf372cc989aaaf94e863fe8582c90` and
parquet-java **1.16.0** at `402c3810c372d29603e181771acebfecc71bef61`
each write complete V1 and V2 files. The two PyArrow row groups exercise
an empty dictionary for an all-null optional column, dictionary reset at
column and group boundaries, and fallback to a PLAIN data page. The Java
files exercise repeated required and optional values across three data
pages per column, including legacy dictionary tags and absent-level tags
in V1. Java statistics remain enabled so its V2 writer emits the actual
null count. Checksums are disabled in all fixtures.

The [oracle][oracle] reads every file with PyArrow, compares every value,
and locates 48 frame windows with Apache Thrift **0.25.0**. It records
absolute offsets, dictionary words, data encodings, and slot counts in
`windows.tsv`. Lean checks the exact observations and all 960 nullable
slots. Regressions also cover swapped or duplicate frames, missing
references, bad metadata offsets and counts, a malformed dictionary body,
CRC rejection, read budgets, and a rejected index stream.

| Fixture | SHA-256 |
| --- | --- |
| `arrow-v1.parquet` | `06321e4fa3ed7d436869d8c6739f31c42c1a619b9db6516f46c0d6c82591277c` |
| `arrow-v2.parquet` | `3705284671a6cf9aaa6ab5242d9f8c361e16b58c64d515b0d16cdb96fe7660f3` |
| `java-v1.parquet` | `f019fd6a0f230fdc60604b5132a6e2c7fb127e91231699697ac94c60e9a5e876` |
| `java-v2.parquet` | `61300a7cc3c87749bd9e7113170573e0e226cabd4485f250923e38d9d91fbdd2` |
| `windows.tsv` | `fc1a6b76c168a00557c383ac6ab24fcd8973b0aa90a0e1e464d92ebc5f4ece44` |

From the repository root, with the [PyArrow and Thrift pins][flat], Maven
and JDK 21 available.

```sh
set -o pipefail
fixture_tmp=$(mktemp -d)
mvn -B -q -f scripts/parquet-dictionary-chunk/pom.xml \
  org.apache.maven.plugins:maven-dependency-plugin:3.8.1:build-classpath \
  -Dmdep.outputFile="$fixture_tmp/classpath"
java -cp "$(cat "$fixture_tmp/classpath")" scripts/parquet-dictionary-chunk/Write.java "$fixture_tmp"
python3 scripts/parquet-dictionary-chunk/Oracle.py "$fixture_tmp" --write-arrow > "$fixture_tmp/windows.tsv"
diff -r --exclude=classpath data/parquet-dictionary-chunk "$fixture_tmp"
lake build --wfail +Silmaril.Formats.Parquet.DictionaryChunk.Thms +Silmaril.Formats.Parquet.DictionaryChunk.Examples
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.DictionaryChunk.Thms +Silmaril.Formats.Parquet.DictionaryChunk.Examples'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-dictionary-chunk/Axioms.lean
```

[matrix]: arrow-parquet-coverage.md
[idl]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift
[dictionary]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#dictionary-encoding-plain_dictionary--2-and-rle_dictionary--8
[framing]: parquet-page-framing.md
[indices]: parquet-dictionary-index.md
[thms]: ../../Silmaril/Formats/Parquet/DictionaryChunk/Thms.lean
[oracle]: ../../scripts/parquet-dictionary-chunk/Oracle.py
[flat]: parquet-flat-page.md#independent-page-fixtures
