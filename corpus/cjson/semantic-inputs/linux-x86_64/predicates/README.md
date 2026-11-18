# cJSON predicate source inputs

`translation-unit.i` is actual host GCC preprocessing of the unchanged cJSON
1.7.19 source. `preprocess-receipt.json` records the executed argument vector,
compiler and package versions, and hashes of all included inputs. Run that
argument vector from the repository root and redirect stdout to reproduce it.
The compiler version and recorded cJSON options match the canonical build;
this was not execution in its pinned container or an ELF rebuild. The canonical
build has no system-header hashes, so identical preprocessing environments are
not established.

`context.c` selects twelve exact byte spans from that translation unit: the
structure, boolean typedef, and ten predicate definitions. `projection.json`
records the spans and hashes. GNU visibility attributes and preprocessor line
markers are retained. This is a declaration dependency closure, not full
translation-unit frontend acceptance or a proof of semantic adequacy of the
projection. The full translation unit still encounters unsupported syntax.

Generate the actual typed Ail and Core documents from this closure with:

```
lake env lean --run tools/corpus/CjsonPredicateInputs.lean
```

The generator uses only the stdlib and implementation maps from the pinned
exported Cerberus runtime in the existing `cast-sign-extend` oracle. Fixture
functions, globals, tags, and expected results are excluded from runtime inputs.
No desired source-to-machine refinement is used as an elaboration assumption.
Kernel elaboration and contextual memory bindings are separate checks; generated
documents and finite executions alone do not establish semantic correctness.

The unchanged original cJSON source license is in the upstream directory.
Expanded system headers retain their source markers; accompanying system-header
license notices are included in `licenses/`.
