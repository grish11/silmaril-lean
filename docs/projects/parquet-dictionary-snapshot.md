# Flat dictionary Parquet snapshots as Arrow batches

`Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary.Defs` opens one
immutable plaintext file as Arrow events. Pass the full physical schema
in wire order to `readAll limits schema bytes`. The adapter supports flat
required and optional INT32, uncompressed PLAIN and dictionary data pages
in V1 and V2. Both branches reject CRC-bearing pages. The PLAIN-only
`Snapshot.FlatInt32.readAll` entry point retains its own profile.
[Dictionary chunk contract][dictionary] · [Snapshot contract][snapshot] · [PLAIN adapter][plain]

## Checked read path

- The byte cap is checked before opening. `Snapshot.check` validates the
  footer, schema and row-group descriptors. Its own limits bound footer
  parsing. `bind` checks the flat leaf list and matches the complete
  ordered schema names once. It checks the file's group, row and cell
  budgets before constructing the indexed decoder. A caller using `bind`
  directly supplies the outer input byte cap.
- The decoder checks the current group's row limit, cell limit and arity
  before dispatch. For each column, it checks the matching path, INT32
  physical type, slot count and codec 0 before consulting the dictionary
  offset. A declared dictionary selects `DictionaryChunk.scanColumn`.
  With no declared dictionary the adapter uses `FlatScan.scanColumn`
  with `decodeInt32Page`. Each branch retains its checked framing, page
  limits, and CRC rejection. A dictionary failure terminates that group.
- The batch assembles the sized columns with `FlatScan.Batch.rows` in
  schema order and binds those rows to the typed Arrow schema. Snapshot
  checks the row count and emits one batch for each successful group,
  including zero-row groups, in footer order. A read error carries the
  group ordinal, column ordinal, field name, and underlying reason. All
  earlier batches are retained. The failing group contributes no rows.
  A malformed footer or schema fails during open, before any batch.

The defaults cap input at 256 MiB, 4,096 groups, 4,194,304 rows, and
16,777,216 cells. The existing PLAIN group and page limits and dictionary
chunk limits govern their respective work. The profile follows the pinned
Parquet Format 2.14.0 and Thrift 0.25.0 rules from the dictionary chunk
contract. Logical projection uses the existing Arrow event APIs.

## Lean contracts

| Theorem | Claim |
| --- | --- |
| `readColumn_dispatch` | Success establishes the matched path/type/count and codec 0, and invokes exactly the selected checked column reader. |
| `scanGroup_ordered` | The assembled columns match the ordered schema and the rows match the declared count. |
| `decodeGroup_rows` | Converting to typed Arrow rows preserves each assembled cell and row position. |
| `readAll_of_openSource` | After a bounded successful open, the result is the checked Snapshot event stream. |
| `collect_first_column_error` | The first failed group keeps the preceding complete rows and reports both original ordinals. |

[Theorem header][thms]

## Independent fixtures

The existing parquet-java **1.16.0** and PyArrow **26.0.1** dictionary files
exercise whole-file V1/V2 reads, all-null slots, dictionary reuse within a
chunk and reset between chunks. The new PyArrow files contain two groups
of eight rows with one required and one optional INT32 column. The positive
file uses a PLAIN required column and dictionary-coded optional column. In
the CRC and Snappy pairs the leading column exercises each declaration.
The oracle verifies every observed value and inspects the actual page
headers with Apache Thrift **0.25.0**. It also independently checks the
stored CRC against each on-disk page body where present.

Thrift locates the first dictionary index width in group 1 at byte 302 of
`mixed-v2.parquet`. Replacing it with 33 keeps the footer and the first
group intact. PyArrow and Lean both read those first eight rows. Lean emits
one eight-row batch and reports `.decode 1 (.column 1 "optional_i32" …)`.
The Lean checks also cover association before offset dispatch, input and
materialization caps, both CRC and codec paths, exact PLAIN compatibility,
and the same empty batch for zero-row writer output.
[Fixture oracle][oracle] · [Lean checks][checks]

| PyArrow 26.0.1 fixture | SHA-256 |
| --- | --- |
| `mixed-v2.parquet` | `b6057176f2e0188f2ff50a435eaf12c993091c848f0d60c39f47118c8da7de9a` |
| `crc-plain-v2.parquet` | `96d05f94ac7970b77fee42ac418f8db799dc88ac68247db3b71974b9f2fce529` |
| `crc-dictionary-v2.parquet` | `d434faec73c2a0bc61184fcd742391ff8aa61d7e10630a1bab0e7377ebda1655` |
| `snappy-plain-v2.parquet` | `15e8036003ce6d4e4bcb25d557ea513c1ca7e7b06b31e9ea4a4ede3f3b0581ab` |
| `snappy-dictionary-v2.parquet` | `626f421c70bfd90114295cc2e648427cd99cee7c89571f113300780cdd7772e1` |

From the repository root with the [PyArrow and Thrift pins][pins] available.

```sh
fixture_tmp=$(mktemp -d)
python3 scripts/parquet-dictionary-snapshot/Oracle.py "$fixture_tmp" --write
diff -r data/parquet-dictionary-snapshot "$fixture_tmp"
lake build --wfail +Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary.Thms +Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary.Checks
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary.Checks +Silmaril.Formats.Parquet.Snapshot.FlatInt32.Checks +Silmaril.Formats.Parquet.DictionaryChunk.Examples parquet-flat-scan-regression'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-dictionary-snapshot/Axioms.lean
```

[dictionary]: parquet-dictionary-chunk.md
[snapshot]: parquet-snapshot.md
[plain]: parquet-flat-arrow.md
[pins]: parquet-flat-page.md#independent-page-fixtures
[thms]: ../../Silmaril/Formats/Parquet/Snapshot/FlatInt32Dictionary/Thms.lean
[oracle]: ../../scripts/parquet-dictionary-snapshot/Oracle.py
[checks]: ../../Silmaril/Formats/Parquet/Snapshot/FlatInt32Dictionary/Checks.lean
