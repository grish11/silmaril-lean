# Bounded Hive manifest inventories

[`Manifest.prepareInventory`](../../Silmaril/Formats/Hive/Manifest/Inventory/Defs.lean)
takes an ordered list of relative paths, the physical schema, a typed
partition schema, Hive path options and a checked converter. Successful
admission produces the same typed file entries as
[`Manifest.prepare`](hive-file-manifest.md), in the order of the selected
occurrences. It uses the ordinary manifest schema check and `prepareFile`.
The entries feed the existing scan and its checked snapshot row denotation.
Their literal paths remain the lookup keys, including percent escapes and
repeated occurrences.

## Profile and failure order

1. Check the schema first, including for an empty inventory or zero budget.
2. Walk the input in order. Each occurrence spends one unit of
   `maxEntries`, including controls and repeated paths. At the boundary an
   empty suffix succeeds. A nonempty suffix yields `entryLimit` at its first
   index, before checking the path there.
3. Check `maxPathBytes` against the UTF-8 byte count of the entire original
   relative path, including slashes, parent directories, the leaf and any
   literal escape bytes. An exact fit succeeds. This is a per-occurrence
   budget. File bytes and converter work are outside these limits.
4. Apply the ordinary manifest's lexical relative-file rules to the whole
   path. The last literal slash separates the parent from the opaque leaf.
   Empty components, dot/dot-dot, literal backslash and NUL are invalid,
   as is a colon in the leaf.
5. Skip the case-sensitive literal leaves `_SUCCESS`, `_metadata` and
   `_common_metadata` at any depth. The leaf is never percent-decoded.
   `%5FSUCCESS`, `_success` and `_metadata.bak` are data declarations.
   A recognized control needs a lexically valid parent. Recognized controls
   bypass Hive parent parsing, partition options and typed cell conversion.
   Thus `other/%GG/_metadata` is skipped and `../_metadata` is a lexical error.
   A control spelling in a parent component has no special status.
6. Use the existing preparation for all data declarations. Parse and render
   the parent with the selected Hive directory profile, then bind the
   nullable cells against the supplied schema. Keep the existing path and
   typed reason inside the new indexed error.

Every per-occurrence error uses the original zero-based position.
Preparation returns the first failure or the complete manifest.
[`prepareInventory_eq_reference`](../../Silmaril/Formats/Hive/Manifest/Inventory/Thms.lean)
equates the one-pass walk with a traversal of the indexed prefix followed
by a suffix check. It compares the full typed file list or error. The
reference uses the same per-entry rules and a separate list traversal.

The caller supplies every occurrence. Directory enumeration, broad
hidden-file filtering, summary-based schema planning and scheduling are
outside this profile.

## Opt-in ordering for a supplied listing

`Manifest.prepareOrderedInventory` uses the same bounded admission before
sorting. A bad declaration still reports its original index, and controls
and repeats still count against the original limits. On success it sorts the
typed files by the full original path using ascending Lean string order.
This compares literal spellings case-sensitively. For example, the percent
sign sorts before a digit and no percent decoding is applied to the sort key.

The sort is stable and retains all occurrences. Distinct spellings with the
same canonical directory stay distinct, and identical literal paths are
kept as repeated scan inputs. The typed partition cells travel with each
file. `Inventory.orderFiles_perm` proves preservation of the full typed list
up to permutation. `Inventory.orderFiles_paths_eq_of_perm` proves that the
sorted lookup sequence depends only on the multiset of admitted keys.
These guarantees concern admitted inputs. Failure precedence follows the
listing's original order.

Callers using the paired checked path ingress can apply `Inventory.orderFiles`
to its successful result. `Inventory.orderFiles_paths` and the paired ingress
path-preservation law show that this supplies the sorted original keys to
the existing paired opener. The scan's action budget applies when callers
run the scan over those entries. All listing enumeration stays with the caller.

## Independent fixture

[Fixture generator](../../scripts/hive-inventory-oracle/Oracle.py) ·
[Checked-in data files](../../tools/parquet-flat-scan/fixtures/hive-inventory) ·
[Hashes for all six fixtures](../../scripts/hive-inventory-oracle/fixtures.sha256)

This uses the [coverage inventory](arrow-parquet-coverage.md#pinned-specifications)
producer pin for PyArrow 26.0.1. Three V1 PLAIN uncompressed Int32 files,
`_metadata`, `_common_metadata` and a zero-byte `_SUCCESS` are generated.
The summary refers to all three data files by their original relative paths.
PyArrow directory discovery supplies the data-file membership. An explicit
scan of those paths in the supplied occurrence order reads
`(10, 7), (20, null), (10, 7), (30, 9)` for `(value, year)`. Passing the
full explicit list fails on `_SUCCESS`. Silmaril admits the mixed inventory
and reads the same ordered nullable rows to EOS using its checked reader.
The opt-in ordering control reverses the supplied listing, then checks
`(10, 7), (10, 7), (30, 9), (20, null)` to EOS. PyArrow supplies the data-file
membership, and the oracle sorts those literal occurrences using UTF-8 bytes
before explicit readback. The oracle exercises the caller's ordering policy.

Spark 4.1.0 evidence comes from source inspection. Spark excludes controls
from data discovery under a broader policy and can use the summaries for
schema planning. [Path filtering](https://github.com/apache/spark/blob/e221b56be7b6d9e48e107fc4d1cf0c15f02700f8/core/src/main/scala/org/apache/spark/util/HadoopFSUtils.scala#L345) ·
[Data-path selection](https://github.com/apache/spark/blob/e221b56be7b6d9e48e107fc4d1cf0c15f02700f8/sql/core/src/main/scala/org/apache/spark/sql/execution/datasources/PartitioningAwareFileIndex.scala#L264) ·
[Summary planning](https://github.com/apache/spark/blob/e221b56be7b6d9e48e107fc4d1cf0c15f02700f8/sql/core/src/main/scala/org/apache/spark/sql/execution/datasources/parquet/ParquetUtils.scala#L66)

To regenerate with CPython 3.14.7, use the image and exact wheel hashes
below. The wheels are the x86-64 binary wheels from PyPI.

| Input | SHA-256 |
| --- | --- |
| `python` image digest | `51dafde81dbdb6ebde285137a295cf18a47ca95234fe388a343719cb97305b3d` |
| `pyarrow-26.0.1-cp314-cp314-manylinux_2_28_x86_64.whl` | `7ae48ab53610b85e004b03bccff593fbdf22186d0ab48ed42c90797915dac814` |
| `numpy-2.5.5-cp314-cp314-manylinux_2_27_x86_64.manylinux_2_28_x86_64.whl` | `c48960d420e90cf305cb1fde0d4e6082cc90512cda87a9acf0b6e04e91cf4abe` |

```sh
tmp="$(mktemp -d)"
docker run --rm --network host -v "$PWD/scripts/hive-inventory-oracle/Oracle.py:/oracle.py:ro" \
  -v "$tmp:/out" python@sha256:51dafde81dbdb6ebde285137a295cf18a47ca95234fe388a343719cb97305b3d \
  sh -ec 'printf "%s\n" \
            "pyarrow==26.0.1 --hash=sha256:7ae48ab53610b85e004b03bccff593fbdf22186d0ab48ed42c90797915dac814" \
            "numpy==2.5.5 --hash=sha256:c48960d420e90cf305cb1fde0d4e6082cc90512cda87a9acf0b6e04e91cf4abe" \
            > /tmp/oracle-requirements.txt
          python -m pip install --only-binary=:all: --require-hashes -r /tmp/oracle-requirements.txt
          python -I /oracle.py /out/fixtures'
(cd "$tmp/fixtures" && sha256sum -c "$OLDPWD/scripts/hive-inventory-oracle/fixtures.sha256")
diff -r -x _SUCCESS -x _metadata -x _common_metadata \
  tools/parquet-flat-scan/fixtures/hive-inventory "$tmp/fixtures"
lake build --wfail +Silmaril.Formats.Hive.Manifest.Inventory.Checks
```
