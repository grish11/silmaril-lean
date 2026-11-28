# Checked Hive Int32 name alignment

[`Manifest.alignedInt32SnapshotOpener`](../../Silmaril/Formats/Hive/Manifest/ParquetSnapshot/AlignedInt32/Defs.lean)
opts into one caller-supplied target data schema across an ordered Hive
manifest. Each target position declares whether its field may be absent.
The adapter uses the existing checked snapshot and flat uncompressed PLAIN
Int32 reader. It binds each file in its complete physical wire order,
resolves target positions by name at open, and remaps rows after decoding
each group. All present physical fields are decoded. Group counts, physical
row counts and the original wire interpretation stay in force.

[`Manifest.flatInt32SnapshotOpener`](../../Silmaril/Formats/Hive/Manifest/ParquetSnapshot/FlatInt32/Defs.lean)
is the strict API and still requires exact ordered physical field names.

## Name and absence policy

- Check the footer and the existing flat Int32 schema before resolving
  any names. That schema check rejects duplicate wire names. The adapter
  then rejects duplicate target names.
- Exact, case-sensitive names identify fields. Before checking extra or
  missing fields, reject any target or wire name reserved by the supplied
  Hive partition schema. This includes wire-only fields. A partition
  constant cannot shadow a physical field.
- Reject an extra wire field. Report the first extra in wire order.
  A projected-out field is still checked and decoded.
- Report the first absent required field in target order. Only positions
  explicitly marked as allowed to be absent receive typed nulls. Required
  here means **required presence in every reached file**, so a present
  physically optional field can still contain a null. The physical reader
  keeps its required-field null checks.
- Name checks occur on open for each reached file. This uses the caller's
  target schema and absence policy. Schema inference, type promotion,
  case folding and column coercion are outside the profile.

The opener uses each occurrence's original path. Standard `Manifest.scan`
keeps occurrence and row order and reports the first open or indexed read
error with its prefix. The existing `scanSkippingRejected` can use this
opener with its usual skip-open policy and its existing EOF-evidence law.
The new theorem below is for the standard scan. Logical projection
happens after the physical read and alignment.

## Laws

- `AlignedInt32.readGroup_alignDecode` maps an existing checked group
  result to target rows with the same row count and read error.
- `AlignedInt32.readAll_alignDecode` emits exactly one aligned batch per
  completed wire group, including empty groups, with the original
  terminal outcome.
- `Manifest.scanAlignedInt32Snapshots_collect_eq_rows` equates the standard
  scan with an independent reference fold. This fold reads the strict
  wire-order groups, resolves each target cell by name, appends the file's
  typed partition constants, and advances only after EOS. Its result
  gives every selected row from completed batches and the exact first
  error. It applies the partition predicate and logical projection in
  row order.
  [Theorem header](../../Silmaril/Formats/Hive/Manifest/ParquetSnapshot/AlignedInt32/Thms.lean)

## PyArrow fixture

[Oracle](../../scripts/hive-int32-alignment-oracle/Oracle.py) ·
[Hashes](../../scripts/hive-int32-alignment-oracle/fixtures.sha256) ·
[Checked-in files](../../tools/parquet-flat-scan/fixtures/hive-int32-alignment)

The [pinned PyArrow 26.0.1](arrow-parquet-coverage.md#pinned-specifications)
oracle writes two files with two groups each. The first has only `id`.
The other has wire order `[latency, id]` and a physical null for `latency`.
Reading `[first, other, first]` with explicit target
`[id, latency, year]` gives these rows in order:

```text
(10, null, 7), (11, null, 7), (20, 200, null), (21, null, null),
(10, null, 7), (11, null, 7)
```

The oracle derives a damaged file with the second group's first page
header replaced by Compact STOP at offset 56. PyArrow independently
reads the first group and reports a page-header error on the second.
The Lean checks apply the same byte mutation, compare the exact
indexed failure and retained batches, and exercise the policy that
requires `latency` when the first file succeeds and the next omits it.

To regenerate, use CPython 3.14.7 from the image digest below and the
hash-pinned x86-64 wheels for PyArrow 26.0.1 and NumPy 2.5.5.

```sh
tmp="$(mktemp -d)"
docker run --rm --network host -v "$PWD/scripts/hive-int32-alignment-oracle/Oracle.py:/Oracle.py:ro" \
  -v "$tmp:/out" python@sha256:51dafde81dbdb6ebde285137a295cf18a47ca95234fe388a343719cb97305b3d \
  sh -ec 'printf "%s\n" \
            "pyarrow==26.0.1 --hash=sha256:7ae48ab53610b85e004b03bccff593fbdf22186d0ab48ed42c90797915dac814" \
            "numpy==2.5.5 --hash=sha256:c48960d420e90cf305cb1fde0d4e6082cc90512cda87a9acf0b6e04e91cf4abe" \
            > /tmp/oracle-requirements.txt
          python -m pip install --only-binary=:all: --require-hashes -r /tmp/oracle-requirements.txt
          python -I /Oracle.py /out/fixtures'
(cd "$tmp/fixtures" && sha256sum -c "$OLDPWD/scripts/hive-int32-alignment-oracle/fixtures.sha256")
diff -r -x year=8 tools/parquet-flat-scan/fixtures/hive-int32-alignment "$tmp/fixtures"
lake build --wfail +Silmaril.Formats.Hive.Manifest.ParquetSnapshot.AlignedInt32.Checks
```
