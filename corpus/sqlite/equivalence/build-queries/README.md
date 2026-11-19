# SQLite build-query binary problems

Seven **unproved** contextual binary-equivalence obligations use six existing
x86-64 shared-library artifacts. No ELF was rebuilt. The registry adds seven
statements (six previous binary statements remain separate), not seven proofs or
new C frontend bindings. The catalog remains 842 artifact rows / 707 hashes.

| Problem | Left | Right | Required signed-int result |
|---|---|---|---|
| versionOptimization | 3.54.1 default O0 | same O2 | 3054001 |
| threadsafeOptimization | 3.54.1 default O0 | same O2 | 1 |
| versionStripping | 3.54.1 default O2 unstripped | same stripped | 3054001 |
| threadsafeStripping | 3.54.1 default O2 unstripped | same stripped | 1 |
| versionConfiguration | 3.54.1 default O2 | 3.54.1 small O2 | 3054001 |
| smallThreadsafeOptimization | 3.54.1 small O0 | same O2 | 0 |
| threadsafeRelease | 3.50.4 default O0 | 3.54.1 default O2 | 1 |

The version query's actual source returns `SQLITE_VERSION_NUMBER`; the threading
query returns `SQLITE_THREADSAFE`. Source definition spans, source hashes, archive
identities, build and runtime receipts, observed flags, ELF hashes, dynamic symbols,
addresses and exact instructions are in `manifest.json` and its referenced public
receipts. This provenance does not replay historical preprocessing or establish
whole-TU frontend adequacy. The threading query says nothing about mutex or
concurrency correctness. Different numeric versions and different THREADSAFE
settings are explicitly excluded from equivalence selection. No inequivalence
proof is supplied either.

Four pairs have different instruction sequences. O0 saves/restores RBP and returns
an immediate; O2 returns an immediate without that frame. The small THREADSAFE=0
O2 query uses `xor eax,eax; ret`. Stripping pairs deliberately retain identical
function bytes inside independently identified ELF files.

`Silmaril.Elf.Corpus.SqliteBuildQueries.Equivalence.Defs` states two independent
`SysV.Implements` obligations for each common deterministic signed-int result.
Neither source refinement nor the desired equality is a premise. Each side must
have a live entry for every (empty) argument tuple, and the safe input domain is
inhabited. Each must terminate at its **first return**, restore callee-saved ABI
state and the stack pointer, be silent apart from core/memory state, and preserve
all memory outside its explicit private frame. Only the eight bytes below entry
RSP used by O0's saved RBP are private; optimized sides have a zero-byte frame.
The return slot, code, globals, heap, permission state and other observable memory
are not arbitrarily hidden. Separate code images are immutable inputs to their
respective caller contexts; code-image equality is not required. There are no
callee contracts or allowed global/heap/I/O effects.

`Equivalence.Thms` kernel-checks real `CodeAt` and dynamic-symbol identity facts for
both queries in all six files. These identity proofs **do not prove** the semantic
obligations. Generated readers retain their generator commands. To regenerate,
run `scripts/corpus/gen_variants.py --artifact PATH` for each of the six exact
`endpoints[].path` values in the manifest, then:

```sh
lake build --wfail Silmaril.Elf.Corpus.SqliteBuildQueries.Equivalence.Thms
python3 -B -m unittest discover -s scripts/corpus -p 'test_*.py'
python3 scripts/corpus/matrix.py --output corpus/matrix.json --check
```

The read-only compiler viewer exports these as **binary** problems, separately
from source/Core contexts and compiler fixtures. It shows both actual function
excerpts, exact contracts and provenance, and links both directions through the
catalog/function routes. No compiler/exporter execution, source-to-instruction
mapping, interactive compilation or proof status is invented. ELF bytes stay in
ordinary artifact files outside the project database.
