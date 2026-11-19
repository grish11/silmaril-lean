# Actual cJSON loop-pair obligation

UNPROVED binary obligation; finite native/Open.step observations are not an equivalence proof.

Finite acyclic allocated lists of length0..64, including a null root; arbitrary admissible aligned heap base and arbitrary unrelated payload bytes.

Both code excerpts share one initial process memory; this is function-level placement, not a whole-ELF segment mapping.

Both actual first returns, ABI preservation, complete region metadata and caller-memory preservation outside exact32/0 private stack frames are obligations.

No desired count, return equality, source refinement, safety or termination is assumed in entry. No callee replacement.

Universal nondeterministic termination/divergence, whole-TU/frontend/build adequacy and general input behavior remain unproved.

Historical cJSON repeat-runtime gaps, unsupported FIPS, distinct jemalloc configurations and repository security alerts remain disclosed.

The original source span and receipts document the observed same-source/default1.7.19 builds; they do not establish source-to-ELF semantic correctness. No new artifact is built. Both actual instruction streams differ (81/35 bytes). The registry and viewer status must remain UNPROVED.

Readable process-memory regions provide the machine heap context. This binary-only problem does not assert a C allocation/provenance interpretation or assume C-to-ELF refinement. The existing separate source context has its own provenance and frontend limitations.

## Reproduce the selected checks

Use this repository's pinned Lean toolchain and public dependencies:

```sh
lake build --wfail Silmaril.Elf.Corpus.CjsonArraySize.Equivalence.Thms
lake env lean -DwarningAsError=true --run tests/cerberus/CjsonArrayEquivalence.lean
python3 -I tools/corpus/check_cjson_array_equivalence_native.py
python3 -m unittest discover -s scripts/corpus -p test_cjson_array_equivalence.py
```

These commands check the existing ELF files and finite executions; they do not
build new corpus artifacts. The machine test executes the exact imported code
placements whose ELF identities are kernel-checked. Child-pointer and unrelated
payload mutations must fail the actual input predicate. The native cases use
contiguous, aligned objects inside the declared address domain.

## Registration and viewer scope

This tranche yields 29 source contexts and 14 registered binary statements.
Eight binary entries have viewer routes: seven SQLite entries and this traversal.
The older five mimalloc and one TinyCC binary statements remain registered but
are not connected to the binary viewer. The 16 compiler fixtures are separate.
All corpus obligations are UNPROVED, with zero corpus semantic proofs. Inventory
remains 842 artifact rows / 707 unique hashes. These are integration counts, not
a claim that this branch has been publicly deployed or that broad function,
variant or semantic coverage is complete.

The exact statement is
`Silmaril.Elf.Corpus.CjsonArraySize.Equivalence.Task.optimization`; its viewer
route is `compiler/?equivalence=` followed by that declaration. Both catalog
artifact/function endpoints link to the same registered problem. The separate
source context is `Silmaril.Elf.Corpus.CjsonArraySize.Context.Task.compilesTo`;
this binary problem assumes neither that source refinement nor its result.
