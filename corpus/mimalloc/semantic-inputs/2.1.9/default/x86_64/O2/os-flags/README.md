# Actual mimalloc Boolean global getters

This public closure selects five exact byte spans from the saved canonical-matching
translation unit shared with `../os-globals/`. It retains the full eight-field
struct and initializer, plus `_mi_os_has_overcommit` and
`_mi_os_has_virtual_reserve`, with their original `_Bool` returns and locations.
No upstream source is rewritten and no new native build is claimed.

`lake env lean --run tools/corpus/MimallocOsFlagInputs.lean` produces typed AIL
and Core using the pinned exported runtime. This is a frontend run, not an
upstream exporter execution. `python3 tools/corpus/check_mimalloc_os_flag_inputs.py`
checks hashes, immutable build/source/ELF pins and the exact projection.
The shared build receipt retains its existing provenance limits.

The contexts describe post-startup canonical Boolean field states, lifetime,
read effects, SysV low-byte Boolean return encoding, and real canonical ELF code.
The raw memory adapter is not claimed to reject every noncanonical `_Bool`
representation; those states are excluded by the contextual entry relation.
These are unproved problems, not semantic proofs or whole-TU adequacy results.
