# Actual SQLite build queries

The saved TU was preprocessed from the unchanged public SQLite 3.54.1
amalgamation using the recorded GCC version and requested canonical flags.
`preprocessing.json` records the command. This current-host preprocessing is
not a replay of the canonical image or proof of historical header identity.
No ELF was rebuilt. Two exact expanded definition spans form `context.c`.

`lake env lean --run tools/corpus/SqliteBuildQueryInputs.lean` computes typed
AIL and Core using the pinned exported runtime. This is an actual frontend
run, not an upstream exporter execution. The immutable inputs and exact spans
are checked by `python3 tools/corpus/check_sqlite_build_query_inputs.py`.

The contexts retain actual no-argument signed-int procedure metadata, no
globals or callees, preserved source memory, SysV return/stack obligations
and real canonical ELF CodeAt at 0x13820 and 0x13830. All refinement problems
remain unproved. The compile-time THREADSAFE value is not a claim about
mutex behavior, concurrent callers or complete SQLite semantics. Exact
projection does not establish whole-TU frontend adequacy or compiler correctness.
