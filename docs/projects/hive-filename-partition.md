# Bounded filename partition prefixes

`PartitionPath.Filename.parse` implements an opt-in subset of
[PyArrow 26.0.1 FilenamePartitioning](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/cpp/src/arrow/dataset/partition.cc#L64-L72).
Use it with `Manifest.prepareInventoryWithFileParser` or
`Manifest.prepareOrderedInventoryWithFileParser`, passing the leaf byte
cap, ordered declared keys, and `.uri` or `.literal` encoding.
Existing directory APIs ignore the leaf. The default still parses the
parent with the checked URI Hive profile.

## Admission

1. The shared inventory checks schema, occurrence budget, and the UTF-8
   byte cap and lexical validity of the full relative file path. Each exact
   literal control leaf (`_SUCCESS`, `_metadata`, `_common_metadata`) is skipped
   before the filename parser runs. Controls count toward the shared
   limits. An encoded or case-altered spelling follows ordinary data
   admission. The parent is lexically checked even for controls.
2. The filename parser checks the UTF-8 byte size of the entire original
   leaf. Its last literal underscore separates the prefix from a required
   nonempty suffix. A leaf without underscores has zero prefix positions.
   Split the prefix on literal underscores and require exactly the
   declared number of nonempty tokens. The suffix is opaque and may have
   any extension. An extra raw underscore in the intended suffix creates
   another prefix token and causes an arity error.
3. Decode the tokens in order using the same checked positional codec as
   [directory partitioning](hive-positional-directory.md). URI mode decodes
   one strict UTF-8 layer after splitting, so `%5f` is an underscore inside
   one value. Literal mode preserves the spelling. No decoding applies
   to the suffix or resolver key. The parent supplies zero partition cells.
4. Every value is present. The typed binder checks the declared column
   names and casts. Sentinel text has the same meaning and the same
   canonical marker collision check as the positional directory profile.
   The canonical directory is internal URI `key=value` metadata.

PyArrow consumes the prefix before the last literal underscore, with
permissive missing and extra positions and some empty tokens. For example,
it reads `west_7_file_name.parquet` as `(west, 7)` with two keys, and it
accepts `west_7_` without a suffix. This profile rejects both. Strict URI
decoding also rejects malformed percent escapes which PyArrow may retain
as text. PyArrow's direct parser interprets `_common_metadata` as a partial
`region=common` key. The shared Silmaril inventory skips that literal
control before parsing. PyArrow's leaf parser disregards parent syntax.
Silmaril applies the existing relative-file lexical checks to the full
path. [Pinned parser and formatter source](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/cpp/src/arrow/dataset/partition.cc#L341-L416)

## Laws and replay

`Filename.parse_ok_iff` specifies the leaf byte cap and exact prefix
admission. `parse_parent_irrel` and `parse_keys_present` establish parent
independence and exact ordered present keys. The shared
`prepareInventory_eq_uri_fileParser` gives the existing default as the
parent-only specialization. `checkEntryWithFileParser_control` proves
that affordable valid controls bypass the selected parser.
`prepareInventoryWithFileParser_eq_reference` and
`prepareInventoryWithFileParser_paths` preserve the exact indexed error
and the complete original data lookup list. The existing bounded
skip-open composition applies through
`prepareOrderedInventoryWithFileParser_scanSkippingRejected_eq_reference`.

[The oracle](../../scripts/hive-filename-path-oracle/Oracle.py) uses
CPython 3.14.7, PyArrow 26.0.1 and NumPy 2.5.5 with the digest and wheel
hashes in the [inventory replay instructions](hive-manifest-inventory.md#independent-fixture).
It uses [pinned Parquet bytes](../../data/parquet-int32-byte-array-file/empty-middle-v2.parquet)
under explicit filename paths with different parents, a duplicate retained
path, and caller-classified controls. Independent readback verifies both
mode-specific cell lists and literal order. Lean checks indexed refusals,
group counts, explicit EOS cost, and complete unmodified lookup spellings.
The profile reads caller-supplied lists and bytes.

```sh
python -I scripts/hive-filename-path-oracle/Oracle.py data/parquet-int32-byte-array-file/empty-middle-v2.parquet
lake build --wfail +Silmaril.Formats.Hive.PartitionPath.Filename.Checks
```
