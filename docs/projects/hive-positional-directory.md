# Bounded positional partition directories

[`PartitionPath.Positional.parse`](../../Silmaril/Formats/Hive/PartitionPath/Positional/Defs.lean)
takes a directory byte cap, an ordered list of partition keys, and a segment
encoding. The function fits `Manifest.DirectoryParser`. Pass it to the
[existing bounded or ordered inventory](hive-manifest-inventory.md#literal-directory-profile)
to bind and scan supplied files.

## Profile

1. Measure the original directory's UTF-8 bytes before splitting. In a
   manifest the existing limits also count all supplied occurrences and
   bound each complete relative file path, including its leaf.
2. Split at literal slash. The empty directory has zero positions. Require
   exactly as many positions as declared keys before decoding. Reject
   empty segments. Delimiters inside percent escapes are interpreted only
   after splitting.
3. URI mode decodes one strict UTF-8 layer using the shared percent codec.
   Literal mode keeps the segment text, matching PyArrow's
   `segment_encoding="none"` convention. An equals sign is ordinary
   positional text. Validate key uniqueness, nonempty keys, and the
   configured required keys.
4. Bind supplied values to the declared keys in positional order. Every
   value is present. The typed binder uses the partition schema's own
   field order and its checked converter. Sorted lookup, duplicates,
   error indices, and bounded skip-open behavior follow the existing laws.

## Pinned PyArrow comparison

The profile shares the text convention of
[PyArrow 26.0.1 DirectoryPartitioning](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/cpp/src/arrow/dataset/partition.cc#L307-L382)
on the checked exact-arity subset. PyArrow accepts missing trailing
positions and ignores extra trailing segments. It can also accept an
empty string slot or malformed percent text. The strict Lean profile
refuses missing, extra, and empty positions and invalid URI escapes.
Both test suites reject invalid decoded UTF-8 in URI mode.

PyArrow's positional reader interprets `__HIVE_DEFAULT_PARTITION__` as
ordinary string text. Its positional formatter can omit trailing nulls
and refuses a later key after a null. The Lean parser never infers null
from a path segment. The shared manifest canonical renderer refuses
present text equal to its configured null marker with
`nullMarkerCollision`. A caller can choose a different, noncolliding
canonical marker to accept this text. The canonical directory is internal
`key=value` metadata. The opener receives the original file string. This
profile covers reading supplied paths and keeps existing URI and literal
Hive defaults. It assumes an explicit key declaration and typed schema.

[`parse_ok_iff`](../../Silmaril/Formats/Hive/PartitionPath/Positional/Thms.lean)
specifies exact arity, the byte cap, and the zip of keys with decoded values.
`parse_keys_present` gives the full ordered key declaration and proves
every value present. Existing `prepareInventoryWith_eq_reference`,
`prepareInventoryWith_paths`, and
`prepareOrderedInventoryWith_scanSkippingRejected_eq_reference` apply to
the positional parser through the shared admission interface.

## Replay

[The oracle](../../scripts/hive-positional-path-oracle/Oracle.py)
uses CPython 3.14.7, PyArrow 26.0.1 and NumPy 2.5.5 with the
[inventory digest and wheel pins](hive-manifest-inventory.md#independent-fixture).
It reads copies of the [pinned Parquet fixture](../../data/parquet-int32-byte-array-file/empty-middle-v2.parquet)
under positional paths in both modes. A reversed listing, duplicate
escaped path, predicate, and control leaf yield the same retained
occurrences, with mode-specific values. PyArrow independently verifies
the rows under explicit caller ordering. Lean checks the aligned
`[3, 0, 2]` repeated group structure and exact final EOS pull.

```sh
python -I scripts/hive-positional-path-oracle/Oracle.py data/parquet-int32-byte-array-file/empty-middle-v2.parquet
lake build --wfail +Silmaril.Formats.Hive.PartitionPath.Positional.Checks
```
