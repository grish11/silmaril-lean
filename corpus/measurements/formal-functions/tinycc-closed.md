# TinyCC closed parameterized function problems

Five exact closed static-inline definitions in the pinned TinyCC 0.9.27 `tcc.h`
are parsed by the actual C frontend: `is_space`, `isid`, `isnum`, `isoct`, `toup`.
Each has one signed int32 parameter and int32 result. Kernel theorems bind the
included raw header span, actual Ail-to-Core elaboration, and selected actual O0
ELF symbol/address/code bytes. No preprocessing or full-TU parse is claimed;
external compilation/configuration correspondence remains provenance evidence.

The statements require valid System V entry/return, first-return termination,
callee-saved preservation, and at most sixteen writable stack bytes, with no
other global/heap/callee/environment effects. Core safety and nonvacuous source
and machine entry remain explicit obligations. All five are stated-unproved.

Selected `.symtab` entries are 50–54 at addresses 29909, 29960, 30011, 30044,
30077. Other same-name local clones are not covered. The database scopes source
statements by exact address and size, and optimization-pair statements by an
address per artifact. Tests check that all other `isnum`/`isid` clones retain
accurate coverage labels.

A sixth new problem compares the selected actual O0 and Og `isid` functions
against the same explicit deterministic ASCII identifier-character predicate,
for every signed int32 input (negative inputs included). The two byte sequences
are independently ELF-bound. X86.Open execution, instruction support and
control-flow correctness are part of the unproved obligation, not certified
by structural parsing or the source/Core checks. No source/semantic correctness assumption or
symbol-name equality is substituted for the unproved machine obligations.

Run `bd1d7897-b063-4795-bfa8-256309085c85` rebuilds all new TinyCC statement,
source-span, source-elaboration and code/symbol binding modules after removing
only their derived `.olean`/trace files from an isolated cache. Dependencies
remain cached. This is actual measured module elaboration/kernel checking,
not merely a cached Lake root check; its cache field is unspecified because
the dependency and target-module cache states differ. The earlier warm root
check and structural receipts are retained separately and are not presented
as fresh kernel replays.

Semantic totals in this tranche: nine distinct C functions / nine contextual
C-to-ELF statements, six binary-equivalence statements, zero semantic proofs.
Three additional delivered TinyCC variants are structurally checked: x86_64 O0
unstripped/stripped and Og unstripped. This tranche alone raises checked variants
96→99; the separate coreutils tranche raises its own baseline 96→208. Combining
both gives 211/416 at this artifact snapshot, with canonical coverage 51/54.

Integration with merged #1064 preserves all 112 coreutils checks: combined variant coverage is 211/416, canonical coverage 51/54.
