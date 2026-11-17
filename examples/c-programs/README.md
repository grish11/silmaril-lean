# C programs through the translation-validation pipeline

Stage 2 of [C translation validation](../../docs/projects/c-tv.md). Each directory holds one
program and every representation the pipeline produced for it, with its provenance. They are
written by `scripts/c-tv/corpus.py`. `make c-tv-check` (part of `make check`) checks that a fresh
run of `ctv-pipeline` on the stored typed Ail and observations gives the stored reports and Core
documents. That check needs neither gcc nor clang.

| File | Stage | Producer | Evidence kind (`TV.Provenance`) |
| --- | --- | --- | --- |
| `source.c` | source | input (`src/<name>.c`) | — |
| `preprocessed.i` | preprocessed | `gcc -E -P -std=c11` | `external` |
| `clang-ast.json.gz` | Clang AST | `clang -x c -std=c11 -target x86_64-linux-gnu -Xclang -ast-dump=json -fsyntax-only` on `preprocessed.i` | `external` (untrusted frontend output) |
| `cerberus.tail.sexp` | typed Ail | `cerb-lean parse --level tail` (the Lean port of Cerberus's frontend) | `compiled` |
| `clang.tail.sexp` | typed Ail | `cfront ail` (fail-closed Clang JSON importer) | `compiled` |
| `<route>.core.sexp.gz` | Core | `ctv-pipeline`: `Elaboration.Functions.elaborate`, `TargetCoherence.linuxLP64`, Cerberus's runtime maps | `compiled` |
| `native-O0.out`, `native-O2.out` | observation | gcc builds of `source.c`, run once | sanity runs, not validation |
| `report.json` | — | `ctv-pipeline run`: explorations, `TV.validate` both ways, `Spec.check` on the observations | `compiled` |
| `provenance.json` | — | every artifact (SHA-256 of the exact bytes; of the uncompressed bytes for `.gz`), its producer and inputs, the edges with their evidence, failures, constructs a route dropped, warnings | — |

A stage that fails leaves its artifact absent and is listed under `failures`. Constructs a route
accepts while dropping them are listed under `losses`. They are never hidden:

* The Cerberus route drops `__asm__` labels and registers, as upstream's `c_parser.mly` does.
* `cfront` drops the attributes it classes as neutral (`used`, `unused`, `deprecated`,
  `noinline`, `always_inline`) and rejects the others, `asm` labels among them.

`cfront` writes `cfront-clang 23.1.0 …` into its documents whatever clang produced the AST. The
pipeline records the clang that actually ran (here Debian clang 19.1.7) in `tools.clang`.

## What the verdicts mean

Every verdict here is computed by compiled Lean code. It is backed by `TV.validate_sound`,
`TV.validate_refuted` and `Spec.check_sound` / `Spec.check_complete` only up to the Lean compiler
and runtime that ran it. These are not kernel-checked instances: the Cores carry Cerberus's
complete runtime library. `cerberus → clang: validated` means that the clang route's Core
refines the Cerberus route's Core: every observation of the one is an observation of the other,
the clang route's Core reaches no gap or stuck state, and it terminates. "Both ways" is
equivalence. This is a translation validation of the two frontends against each other through
the same elaborator. It is not a proof that either frontend implements C. `gcc -O0 exit 37:
admitted` means that the exit status and stdout of one run of the gcc binary are an observation
the Core allows (`Spec.check`). That is one execution of one build, not a compiler correctness
result.

The profile is `linuxX86_64` (`Silmaril.Project.Shapes.CTV`). Coherence is necessary, not
sufficient. None of the elaborated programs has `float`, `long double` or `wchar_t` objects.

## The corpus (24 programs)

"Agree" is a **frontend agreement**: each route's Core refines the other's (Core to Core, through
the same elaborator), checked with `TV.validate` both ways; "UB-free" means each source
exploration was exhaustive without undefined behaviour (`validateUBFree`). A verdict that rests
on source undefined behaviour is labelled so and never counted as a validation of defined
behaviour. "Profile does not apply" means the Core mentions a type at which the x86-64 profile is
not coherent (per type, `TV.Profile.AppliesTo`; `report.json` lists the mentions and blockers).

| Program | Cerberus route | Clang route | Frontend agreement | Native runs | Dropped |
| --- | --- | --- | --- | --- | --- |
| `arithmetic` | Core: defined 37 | Core: defined 37 | agree both ways (UB-free) | gcc-O0 exit 37: admitted by both Cores; gcc-O2 exit 37: admitted by both Cores |  |
| `asm-label` | Core: defined 7 | frontend rejects | — | gcc-O0 exit 7: cerberus admitted; gcc-O2 exit 7: cerberus admitted | cerberus drops asm label or register |
| `attribute` | frontend rejects | Core: defined 42 | — | gcc-O0 exit 42: clang admitted; gcc-O2 exit 42: clang admitted | clang drops attribute |
| `calls` | Core: defined 5 | Core: defined 5 | agree both ways (UB-free) | gcc-O0 exit 5: admitted by both Cores; gcc-O2 exit 5: admitted by both Cores |  |
| `compare` | Core: defined 2 | Core: defined 2 | agree both ways (UB-free) | gcc-O0 exit 2: admitted by both Cores; gcc-O2 exit 2: admitted by both Cores |  |
| `control-flow` | elaborator rejects | elaborator rejects | — | gcc -O0 exit 6 (no Core to check) |  |
| `division-by-zero` | elaborator rejects | elaborator rejects | — | gcc -O0 signal 8 (no Core to check) |  |
| `float` | elaborator rejects | elaborator rejects | — | gcc -O0 exit 3 (no Core to check) |  |
| `globals` | elaborator rejects | elaborator rejects | — | gcc -O0 exit 5 (no Core to check) |  |
| `local-if` | Core: defined 12 | elaborator rejects | — | gcc-O0 exit 12: cerberus admitted; gcc-O2 exit 12: cerberus admitted |  |
| `locals` | elaborator rejects | elaborator rejects | — | gcc -O0 exit 17 (no Core to check) |  |
| `nested-calls` | Core: defined 42 | Core: defined 42 | agree both ways (UB-free) | gcc-O0 exit 42: admitted by both Cores; gcc-O2 exit 42: admitted by both Cores |  |
| `overflow-return` | Core: ub | Core: ub | agree only through source UB | gcc-O0 exit 0: admitted by both Cores; gcc-O2 exit 0: admitted by both Cores |  |
| `pointer` | elaborator rejects | elaborator rejects | — | gcc -O0 exit 3 (no Core to check) |  |
| `recursion` | elaborator rejects | elaborator rejects | — | gcc -O0 exit 20 (no Core to check) |  |
| `return-constant` | Core: defined 42 | Core: defined 42 | agree both ways (UB-free) | gcc-O0 exit 42: admitted by both Cores; gcc-O2 exit 42: admitted by both Cores |  |
| `sign-extend` | Core: defined -1 | Core: defined -1 | agree both ways (UB-free) | gcc-O0 exit 255: admitted by both Cores; gcc-O2 exit 255: admitted by both Cores |  |
| `signed-narrow` | Core: defined -56 | Core: defined -56 | agree both ways (UB-free) | gcc-O0 exit 200: admitted by both Cores; gcc-O2 exit 200: admitted by both Cores |  |
| `signed-overflow` | elaborator rejects | elaborator rejects | — | gcc -O0 exit 0 (no Core to check) |  |
| `statement-expression` | frontend rejects | elaborator rejects | — | gcc -O0 exit 6 (no Core to check) |  |
| `unsequenced-calls` | elaborator rejects | elaborator rejects | — | gcc -O0 exit 12 (no Core to check) |  |
| `unsequenced-ub` | elaborator rejects | elaborator rejects | — | gcc -O0 exit 3 (no Core to check) |  |
| `unsigned-parameter` | Core: defined 1 | Core: defined 1 | agree both ways (UB-free) | gcc-O0 exit 1: admitted by both Cores; gcc-O2 exit 1: admitted by both Cores |  |
| `unsigned-wrap` | Core: defined 2 | Core: defined 2 | agree both ways (UB-free) | gcc-O0 exit 2: admitted by both Cores; gcc-O2 exit 2: admitted by both Cores |  |

Most rejected programs stop at the elaborator, which covers selected cases of upstream's
`translation.lem` only: non-`return` statements, loops, division and remainder, floating constants
and initialized non-arithmetic locals are among the rejected forms
([cerberus.md](../../docs/projects/cerberus.md#status)). `signed-narrow` exercises an
implementation-defined conversion (C11 §6.3.1.3p3): both Cores give −56, and the gcc runs exit
with 200, which the Cores admit. `overflow-return` is the one program whose agreement rests on
undefined behaviour. The other UB programs (`signed-overflow`, `unsequenced-ub`,
`division-by-zero`) are rejected before any verdict exists, and their native runs say nothing
about C.
