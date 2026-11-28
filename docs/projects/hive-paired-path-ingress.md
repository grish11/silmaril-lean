# Checked path ingress for the Hive INT32 and BYTE_ARRAY pair

`Manifest.Int32ByteArray.Ingress.preparePaths` takes a declared selected
physical pair, a typed partition schema, Hive path options, and an ordered
list of literal relative file paths. It produces ordinary
`Manifest.File` values for the existing paired snapshot opener, strict scan,
and opt-in budget and pruning functions.

The builder uses the existing Hive name, lexical, percent-decoding, and
typed-binding rules. The original string, including the leaf spelling, is
the lookup key. Canonicalization applies to the directory stored alongside
it. Repeated declarations remain separate occurrences. Virtual cells follow
the declared partition schema even when keys appear in a different path
order. Physical columns keep their existing positions. The builder checks
partition names against the declared selected pair. The paired snapshot
opener also checks all leaves, including unselected ones, after reading the
physical schema.

## Admission and failure order

1. Check the partition schema and its names against the selected pair,
   including for an empty list.
2. In supplied order, split each path, parse and render its directory with
   the supplied options, and bind its partition cells. Path syntax and
   key admission come before field binding. Binding reports missing keys and
   cast errors in declared field order, using `PrepareError` with the
   original path. The options' required keys apply during path parsing.
3. After binding one occurrence, reject the first null required cell in
   declared field order with `requiredNull path field`. An earlier binding
   error on that occurrence takes precedence over any required-null check.
   Return the first failing occurrence and stop admission.

Present INT32 values accept ASCII decimal digits with an optional leading
minus and must fit the signed range. Syntax failures carry the decoded text
and range failures carry the mathematical integer. BYTE_ARRAY values are the
UTF-8 bytes of decoded path text. An empty decoded label is present empty
bytes. The configured marker is compared after percent decoding. A missing
key uses its declared missing policy, so `reject` yields the existing missing
key error and `asNull` yields a nullable cell. The final required check rejects
both explicit and synthesized nulls for required kinds. This extra check is
specific to the opt-in builder.

`preparePaths_ok_iff` characterizes successful output as the exact files from
generic `Manifest.prepare` with the checked converter, with every required
cell present. `preparePaths_preserves_paths` preserves the full literal
occurrence list. `convert_int32_ok_iff` relates every successful cast to the
exact mathematical integer and `convert_byteArray` specifies the UTF-8 mapping.

## Bounded scan from supplied paths

`Manifest.Int32ByteArray.Ingress.scanPaths` takes the same declarations and an
explicit open policy. Both policies admit the entire list before applying
the partition predicate or using the scan-action budget. A malformed path,
invalid cast, or required-null failure therefore aborts admission even at
budget zero or when its partition would otherwise be rejected. An ingress
error carries the original typed cause and produces no trace. After
admission, lookup and Parquet failures are typed terminal outcomes in the
trace, which retains whatever selected batches were already emitted.

Strict traversal opens each reached literal occurrence, including rejected
partitions. Skip-open traversal stably removes rejected occurrences after
admission. Its budget pays only for the remaining opens, group pulls, and
explicit file EOS pulls. Repeated retained paths keep separate positions and
charges. The budget counts logical traversal actions. Path admission has no
action charge and the budget makes no bound on physical work or bytes.

`scanPaths_error_iff` gives exact ingress failure and `scanPaths_ok_iff`
identifies the full result with bounded traversal of the admitted list (or
its stable filter), preserving original path spellings. The existing bounded
trace, cutoff, and prefix laws apply to that list with the same budget.
Paired fixture guards distinguish rejected malformed input from an admitted
rejected file with corrupt Parquet data, and exercise a repeated retained
literal, empty batches, and the exact EOS cutoff at zero projection width.

## Independent replay

The [oracle](../../scripts/hive-paired-ingress-oracle/Oracle.py) copies the
existing [pinned Parquet fixture](../../data/parquet-int32-byte-array-file/empty-middle-v2.parquet)
under four literal Hive declarations in a temporary directory. PyArrow
verifies five partitioned rows per declaration, projected in declared
partition order, plus exact footer group sizes `[3, 0, 2]`. It exercises
reversed path keys, escaped UTF-8 and slash, both INT32 endpoints, missing
keys, the escaped default marker, and present empty text. Separate PyArrow
parse controls reject both overflows and malformed numerals. The Lean guards
check exact error constructors and required-null policy, literal duplicate
ordering and exact group boundaries in a paired scan. The external replay
checks values per file.

Use CPython 3.14.7 (image digest
`sha256:51dafde81dbdb6ebde285137a295cf18a47ca95234fe388a343719cb97305b3d`)
on linux/amd64 and the following wheel hashes.

```text
c48960d420e90cf305cb1fde0d4e6082cc90512cda87a9acf0b6e04e91cf4abe  numpy-2.5.5-cp314-cp314-manylinux_2_27_x86_64.manylinux_2_28_x86_64.whl
7ae48ab53610b85e004b03bccff593fbdf22186d0ab48ed42c90797915dac814  pyarrow-26.0.1-cp314-cp314-manylinux_2_28_x86_64.whl
```

```sh
python -m pip install --no-index --find-links /wheels pyarrow==26.0.1 numpy==2.5.5
python -I scripts/hive-paired-ingress-oracle/Oracle.py \
  data/parquet-int32-byte-array-file/empty-middle-v2.parquet
```

Ingress works on caller-supplied strings. The relative path profile, generic
inventory admission, reader limits, physical BYTE_ARRAY decoding, and scan
contracts apply as documented by their current APIs.
