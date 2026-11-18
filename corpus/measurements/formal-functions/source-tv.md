# First concrete source-to-ELF problem

The pinned mimalloc 2.1.9 x86_64 O2 `mi_version` function now has one concrete contextual C-to-ELF obligation. It is stated and unproved. The existing O0/O3 function-equivalence problem is also stated and unproved; neither is a semantic proof.

The included actual preprocessed TU comes from an observation build that reproduced the canonical ELF SHA256. Lean kernel checks the exact 39-byte closed definition span (including its newline), checks the actual Ail-to-Core elaboration, and checks canonical function code bytes at virtual address 0xe2b0 and the parsed exported symbol name/address/size/kind. The actual source frontend is checked by compiled evaluation, not claimed as a kernel theorem. The external GCC preprocessing and build receipt remain provenance trust boundaries. No full-TU semantic validation is claimed.

The explicit contract is System V AMD64, no arguments, int32 return, Open/Ext8 execution, valid machine entry/return address, code disjointness, zero writable stack frame below entry RSP, restored callee-saved registers, no globals/callees/heap/environment effects. The actual Core procedure is selected by name from elaborated source. The obligation includes the source elaboration condition, and the machine contract requires nonvacuous safe source meaning/enterability.

Verification: targeted --wfail root passed, measured 12.605s wall; source projection has no axioms, elaboration/code binding use only propext/Classical.choice/Quot.sound. Receipt and exact input hashes are in corpus/measurements/formal-functions. No new axiom, sorry, native_decide or CI threshold change.

Coverage remains narrow: one closed literal-return C function and one separate binary-equivalence problem. The full corpus request still requires memory/call semantics, more functions/configurations and checked variant decompositions.

The closed-leaf extension adds `_mi_arena_id_none` (int result) and `_mi_allocator_done` (void fallthrough) from actual saved preprocessing, with checked source span(s), actual frontend/Core elaboration, ELF bytes and local symbol identities. Their contextual machine obligations remain unproved. Total: three distinct C functions, three C-to-ELF statements and one binary-equivalence statement; zero semantic proofs. `blockers.json` records inspected unsupported candidates without counting them as statements.
