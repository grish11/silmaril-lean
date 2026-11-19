# Corpus statements in the compiler viewer

These bounded manifests select public inputs for every contextual statement in
`corpus/measurements/formal-functions/checks.json`. They are separate from the
compiler fixtures and their exporter/proof evidence. Every corpus refinement
remains **UNPROVED**; no program-point map or interactive compiler is supplied.

`tools/compiler-explorer/corpus.py` checks registered file pins, exact source
projection spans, catalog identities, actual ELF function symbols and executable
segment bytes. It exports one small JSON record per statement and deduplicated
hash-addressed text files. ELF files stay in Git, outside the database. Text input
is bounded to 2 MiB per resource and machine-code excerpts to 64 KiB. This Python
identity check is not kernel replay or a new compiler/Lean exporter run.

The Core pane shows the recorded serialized input together with its actual Lean
defining modules. In older closed-leaf statements the existing `fixRet` step is
visible in those modules; the raw serialized input is not misrepresented as a new
elaboration result. Shared cJSON/global closures display all included procedures,
not invented source-line/instruction correspondences. ABI, initialized memory,
callee, UB and provenance obligations remain in the exact linked definitions.

Pages generation runs this export after public catalog generation. Artifact and
function pages use registered declaration identities as viewer links. Regression
coverage checks actual cJSON pointer and mimalloc global cases through the full
artifact/function → statement → source/Core/ELF → artifact/function roundtrip.

Binary-to-binary problems use the separate bounded `tools/compiler-explorer/equivalence.py` export and `?equivalence=` viewer routes. The SQLite pair manifest is `corpus/sqlite/equivalence/build-queries/manifest.json`; these are unproved ABI/memory obligations, not source/Core fixtures. Existing six binary statements without pair manifests are not silently converted to viewer evidence.
