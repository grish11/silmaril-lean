# Typed Hive virtual partition columns

An ordered manifest supplies decoded Hive partition entries and already
available physical rows. `prepare` checks the partition schema and decodes
every entry. `materialize` appends the typed partition cells to each physical
row. The result uses the existing nullable table and schema from
`Silmaril.Relational.Scan`. [Definitions](../../Silmaril/Formats/Hive/TypedPartitions/Defs.lean) ·
[Shared scan API](../../Silmaril/Semantics/Relational/Scan/Defs.lean) ·
[Hive directory paths](hive-partition-path.md)

## Policies

| Input | Policy |
| --- | --- |
| Column order and identity | Physical columns come first, in their original order. A `PartitionSchema` stores the virtual fields in an ordered array. Decoded key order has no effect on virtual column order. Names are compared case-sensitively. |
| Schema validity | Virtual names must be nonempty and unique. Any virtual name equal to a physical column name is rejected, regardless of type. Existing physical identities and positions are preserved. Schema validation runs even on an empty manifest. |
| Partition keys | Reject empty keys, duplicate decoded keys and unknown keys. Each field chooses either `Missing.reject` or `Missing.asNull`. A present null satisfies either policy. |
| Conversion | A caller supplies a checked `Convert` function that receives the field and its text, returning a value of the field's declared kind or a caller-defined error. Explicit and synthesized nulls skip conversion. Present empty text goes to the converter unchanged. A conversion failure reports the field and the caller's reason. |
| Validation order | Process partitions in manifest order. Validate the keys in each binding before converting fields in declared schema order. Report the first error and produce no typed manifest. These checks also apply to partitions with zero rows. |

The lexical module supplies decoded entries, including its default marker
policy. Callers can also supply entries directly. The typed layer validates
those entries independently and treats every `some text` as present text.
It does not compare text with a null marker again.

## Guarantees

- `prepare_preserves_rows` preserves the ordered list of physical tables on
  successful preparation, including empty partitions.
- `physicalCells_extendRow` recovers the original physical row.
  `partitionCells_extendRow` recovers the nullable virtual tuple used to
  extend it.
- `materialize_preserves_order` recovers the concatenated physical rows in
  manifest order and in each partition's row order. It preserves duplicates.
  `materialize_rowCount` gives the sum of the physical row counts, including
  with a zero-column schema.
- `scanPartitions_eq_scan` evaluates a partition-only predicate once per
  manifest entry. Its ordered projected result equals the shared logical scan
  that evaluates the predicate on each augmented row. True keeps rows. False
  and unknown discard them. The theorem allows arbitrary output projection.

The scan equality is over successfully prepared manifests containing physical
rows. File discovery, reads and their errors are outside the model. Skipping
a file before opening it would require a separate result and error contract.
[Theorem header](../../Silmaril/Formats/Hive/TypedPartitions/Thms.lean)

## Checks

```sh
lake build --wfail +Silmaril.Formats.Hive.TypedPartitions.Checks
make check CHECK_TARGETS=+Silmaril.Formats.Hive.TypedPartitions.Checks
```

The checks exercise empty manifests and partitions, zero-column rows,
duplicate rows, ordered and reordered columns, true/false/unknown selection,
missing and duplicate keys, physical collisions, null versus empty text, and
typed conversion errors. They also print the axiom dependencies of the public
theorems. [Regression checks](../../Silmaril/Formats/Hive/TypedPartitions/Checks.lean)
