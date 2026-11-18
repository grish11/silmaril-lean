# Concrete function statements

One stated, unproved binary functional-equivalence problem: delivered mimalloc 2.1.9 x86_64 O0 and O3 `mi_version` functions implement the same deterministic System V int32 result219. This is stronger than comparing symbol names/bytes: the problem requires each placed function's first-return total correctness, valid ABI entry, callee-saved register restoration and no writes outside eight stack bytes below entry. There are no arguments/global/heap/callee/environment effects in the required contract. This describes the obligation, not a proved property.

`CodeAt` and exported-symbol identity theorems are kernel checked against both actual ELF files. The shared contract is deterministic, so it cannot hide distinct results behind a nondeterministic specification. This is not a C-to-ELF statement; no arbitrary Core is bound as source semantics. Contextual C-to-ELF count remains0, binary-equivalence statements1, semantic proofs0.

`checks.json` binds exact ELF/module hashes and the successful --wfail run receipt. One declaration mentions two artifacts; global counts deduplicate it, while both artifact pages link it. Changing a bound module/ELF invalidates the recorded check. The separate actual frontend/Core probe for the pinned preprocessed C definition remains in progress.

Successful statement/ELF-binding check: run6d3b930c-cbbd-49bc-b033-933acdead32a,4.801s wall /2,435,708KiB peak child RSS, one worker, warm dependencies. `#print axioms` of the code bindings reports only propext/Classical.choice/Quot.sound; exported-symbol identity checks use no axioms. No new axiom, sorry or native_decide is used.
