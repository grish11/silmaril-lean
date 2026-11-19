# Concrete function statements

`checks.json` is the authoritative registry of concrete statement declarations,
statuses, exact ELF/source/module hashes and successful `--wfail` root receipts.
Global counts deduplicate declarations; each participant artifact links the same
statement. Changes to bound inputs invalidate the recorded check.

The contextual C-to-ELF problems use actual frontend-produced typed Ail and
kernel-checked Core elaboration. Source spans are bound to included upstream or
saved preprocessing, and actual ELF code placements are checked separately.
See `source-tv.md` and the source modules for the precise provenance boundaries.
Source preprocessing/build correspondence is external evidence; it is not a
kernel proof of the external compiler or a full translation-unit frontend claim.

The mimalloc binary-equivalence problems require both actual functions to
implement the same deterministic System V int32 result meaning (219). They
require valid loaded entry, first-return termination, preserved callee-saved
registers and no writes outside the permitted stack frame. They compare the
O0/O3 functions and four stripped/unstripped optimization pairs. Paired receipt
metadata locates stripped functions; no stripped symbol table is invented.
See `mimalloc-stripping.md` for the additional pairs.

All registered semantic obligations are **stated-unproved**. Successful root
checks establish well-formed statements and their source/ELF bindings, not
semantic correctness. Semantic proofs remain zero. Context-only rows and
unsupported candidates are not counted as concrete statements. `blockers.json`
is an inspected sample of unsupported functions, not a whole-corpus census of
frontend/model support.

No new axiom, `sorry` or `native_decide` is used. The checked code-placement and
Core-elaboration theorems use only the allowed standard axioms; concrete symbol
identity equations use none. Timing receipts describe their actual runs and
cache state, not hypothetical future performance.
