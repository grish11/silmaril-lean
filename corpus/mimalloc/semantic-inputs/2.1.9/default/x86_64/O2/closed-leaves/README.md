# Actual closed mimalloc definitions under test

`arena.i` and `prim_prim.i` are saved preprocessing from the same pinned observation build that reproduced canonical mimalloc byte-for-byte. Existing `../mi_version/source-binding.json` and compressed log retain the exact image, upstream and compiler command inventory; these copies introduce no new clean-repeat/timing claim. The existing system-header licences and mimalloc MIT notice apply.

`_mi_arena_id_none.c` joins the exact existing `typedef int mi_arena_id_t;` span to the exact closed definition from arena.i. Both spans are kernel checked individually; no guessed typedef or text rewrite is used. `_mi_allocator_done.c` is the exact empty void definition span from prim_prim.i. Full translation-unit frontend parsing is not claimed. External GCC preprocessing/build provenance remains a trust boundary.

Both actual frontend outputs elaborate to the quoted Core (kernel checked). The canonical function bytes and local ELF symbol identities are checked. The two contextual C-to-ELF statements are unproved. They cover System V AMD64/no arguments, zero writable stack frame, preserved callee-saved registers, first-return termination and no globals/calls/heap/environment effects; they do not validate the allocator. The void function needs the ordinary void-fallthrough port in #1044.
