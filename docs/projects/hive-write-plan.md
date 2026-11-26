# Pure Hive write planning

[`Hive.WritePlan.plan`](../../Silmaril/Formats/Hive/WritePlan/Defs.lean)
routes an ordered typed table to relative Hive directories and physical
row tables. The source schema extends the physical schema with the
explicitly supplied partition schema. Physical cells are preserved in
their original column order. A zero-column physical payload retains its
row count through the row list.

## Admission and errors

1. Check partition names and physical-name collisions using
   `TypedPartitions.checkSchema`, including on empty input.
2. Visit input rows in order. For each row, encode present virtual cells
   with the caller's checked dependent encoder in declared field order.
   Null bypasses the encoder. Encoder failure names the field and retains
   the caller's typed reason.
3. Render those entries with the existing `PartitionPath.render` policy.
   This checks required keys and rejects a literal cell whose encoded text
   equals the configured null marker. Parse the rendered directory using
   `PartitionPath.parse` with the same options before admitting the row.
   Path options apply to each row's directory. An empty table produces
   an empty plan after the schema check.
4. Group by exact rendered directory in first-occurrence order. Inside
   each group, preserve relative input order and every duplicate row.
   An empty partition schema routes rows to the dataset root.

A row failure reports its original zero-based index and its encoder,
render or parse error. The plan is returned only on complete success.
A caller can hand each physical table to a writer. Filename allocation,
file writes and catalog updates are outside this API. The grouping uses
the encoder's text as the key. Recovering typed virtual values on readback
additionally requires a suitable inverse for the caller's encoder.

The planner uses a stable partition of the remaining classified rows for
each directory. It makes at most one pass over the remaining rows for
each distinct directory. The plan groups interleaved input
rows, so only per-directory row order and first occurrence of directories
are guaranteed.

## Laws

[`plan_eq_reference`](../../Silmaril/Formats/Hive/WritePlan/Thms.lean)
equates the full result to an independent grouping that takes the
first-seen unique directory list and filters the original classified
rows once for each directory. Both use the checked classification above.

`plan_first_row_error_iff` characterizes exactly when the planner returns
a row error. The schema check succeeds, the index equals the length of an
all-successful input prefix, and classification of the next row gives the
same typed reason.

## Typed reconstruction

[`WritePlan.restore`](../../Silmaril/Formats/Hive/WritePlan/Restore/Defs.lean)
checks the supplied schema and parses and binds each bucket's directory
in order. It attaches the resulting typed partition tuple to every
physical row of the bucket using the existing typed materializer.
A path or binding error carries the bucket's literal directory and
the original error. The operation also accepts caller-supplied buckets.

[`restore_plan_eq_groupedRows`](../../Silmaril/Formats/Hive/WritePlan/Restore/Thms.lean)
states the result for a successful plan. Planning and restoration use
the same physical schema, partition schema, and path options. The only
codec premise is a left inverse for successful present-cell encodings.

```text
For each declared field and each present value and text,
  encode(field, value) = ok(text) implies decode(field, text) = ok(value).
```

Nulls are explicit in the partition entries and bypass both callbacks.
Successful planning supplies render admission, including the configured
nonempty null marker, required keys, and rejection of literal sentinel
collisions. [`PartitionPath.parse_render_of_ok`](../../Silmaril/Formats/Hive/PartitionPath/Thms.lean)
proves exact entry recovery under those same options. The left inverse
then ensures that a shared directory reconstructs the original tuple
for every row routed there. Successful planning by itself permits a
lossy caller encoder. A Lean regression demonstrates this by encoding
the original text as `fixed` and recovering that replacement.

The theorem equates restoration to grouping the *full original rows*
by their admitted directories. It preserves first-seen directory order,
within-directory row order, duplicates, and nullable typed cells.
Grouping changes the order of interleaved directories.

The [reconstruction checks](../../Silmaril/Formats/Hive/WritePlan/Restore/Checks.lean)
read the five [pinned PyArrow files](../../tools/parquet-flat-scan/fixtures/hive-write-plan)
in explicit first-seen directory order with the existing flat Int32
reader. They compare the parsed and typed result to the grouped input.
The same fixture generator and hashes below verify membership and
bytes independently. Lean alone asserts reconstruction order.

## Pinned checks

[PyArrow membership oracle](../../scripts/hive-write-plan-oracle/Oracle.py) ·
[Parquet hashes](../../scripts/hive-write-plan-oracle/fixtures.sha256) ·
[Lean checks](../../Silmaril/Formats/Hive/WritePlan/Checks.lean)

The supported-domain fixture uses [pinned PyArrow 26.0.1](arrow-parquet-coverage.md#pinned-specifications)
with nullable UTF-8 and Int32 virtual cells. It checks five literal
directories and compares physical and logical row membership with
multiplicities. The rows include escaped slash and equals, Japanese text,
null, empty text and an interleaved repeated row. Separate Lean guards
assert first-directory occurrence and stable row order. The sentinel
collision is a Lean rejection with an exact index and key.

To regenerate, use the CPython 3.14.7 image and hash-pinned x86-64 binary
wheels below.

```sh
tmp="$(mktemp -d)"
docker run --rm --network host -v "$PWD/scripts/hive-write-plan-oracle/Oracle.py:/Oracle.py:ro" \
  -v "$tmp:/out" python@sha256:51dafde81dbdb6ebde285137a295cf18a47ca95234fe388a343719cb97305b3d \
  sh -ec 'printf "%s\n" \
            "pyarrow==26.0.1 --hash=sha256:7ae48ab53610b85e004b03bccff593fbdf22186d0ab48ed42c90797915dac814" \
            "numpy==2.5.5 --hash=sha256:c48960d420e90cf305cb1fde0d4e6082cc90512cda87a9acf0b6e04e91cf4abe" \
            > /tmp/oracle-requirements.txt
          python -m pip install --only-binary=:all: --require-hashes -r /tmp/oracle-requirements.txt
          python -I /Oracle.py /out/fixtures'
(cd "$tmp/fixtures" && sha256sum -c "$OLDPWD/scripts/hive-write-plan-oracle/fixtures.sha256")
diff -r tools/parquet-flat-scan/fixtures/hive-write-plan "$tmp/fixtures/data"
lake build --wfail +Silmaril.Formats.Hive.WritePlan.Checks +Silmaril.Formats.Hive.WritePlan.Restore.Checks
```
