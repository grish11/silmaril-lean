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

## The corpus (16 programs)

| Program | Cerberus route | Clang route | Cross-validation | Native runs | Dropped |
| --- | --- | --- | --- | --- | --- |
| `arithmetic` | Core: defined 37 | Core: defined 37 | validated both ways | gcc-O0 exit 37: admitted by both Cores; gcc-O2 exit 37: admitted by both Cores |  |
| `asm-label` | Core: defined 7 | frontend rejects | — | gcc-O0 exit 7: cerberus admitted; gcc-O2 exit 7: cerberus admitted | cerberus drops asm label or register |
| `attribute` | frontend rejects | Core: defined 42 | — | gcc-O0 exit 42: clang admitted; gcc-O2 exit 42: clang admitted | clang drops attribute |
| `calls` | Core: defined 5 | Core: defined 5 | validated both ways | gcc-O0 exit 5: admitted by both Cores; gcc-O2 exit 5: admitted by both Cores |  |
| `control-flow` | elaborator rejects | elaborator rejects | — | gcc -O0 exit 6, -O2 exit 6 (no Core to check) |  |
| `division-by-zero` | elaborator rejects | elaborator rejects | — | gcc -O0 signal 8, -O2 signal 4 (no Core to check) |  |
| `float` | elaborator rejects | elaborator rejects | — | gcc -O0 exit 3, -O2 exit 3 (no Core to check) |  |
| `globals` | elaborator rejects | elaborator rejects | — | gcc -O0 exit 5, -O2 exit 5 (no Core to check) |  |
| `locals` | elaborator rejects | elaborator rejects | — | gcc -O0 exit 17, -O2 exit 17 (no Core to check) |  |
| `pointer` | elaborator rejects | elaborator rejects | — | gcc -O0 exit 3, -O2 exit 3 (no Core to check) |  |
| `recursion` | elaborator rejects | elaborator rejects | — | gcc -O0 exit 20, -O2 exit 20 (no Core to check) |  |
| `return-constant` | Core: defined 42 | Core: defined 42 | validated both ways | gcc-O0 exit 42: admitted by both Cores; gcc-O2 exit 42: admitted by both Cores |  |
| `signed-overflow` | elaborator rejects | elaborator rejects | — | gcc -O0 exit 0, -O2 exit 0 (no Core to check) |  |
| `statement-expression` | frontend rejects | elaborator rejects | — | gcc -O0 exit 6, -O2 exit 6 (no Core to check) |  |
| `unsequenced-calls` | elaborator rejects | elaborator rejects | — | gcc -O0 exit 12, -O2 exit 12 (no Core to check) |  |
| `unsequenced-ub` | elaborator rejects | elaborator rejects | — | gcc -O0 exit 3, -O2 exit 3 (no Core to check) |  |

Twelve of the 16 programs stop at the elaborator. It covers only selected cases of upstream's
`translation.lem`: non-`return` statements, loops, division and remainder, floating constants and
initialized non-arithmetic locals are among the rejected forms ([cerberus.md](../../docs/projects/cerberus.md#status)).
The UB programs (`signed-overflow`, `unsequenced-ub`, `division-by-zero`) are rejected before any
UB verdict exists. Their native runs are recorded but say nothing about C.
