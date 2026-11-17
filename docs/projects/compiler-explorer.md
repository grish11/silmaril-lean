# A verified compiler explorer: problems, mappings, comorphisms

A compiler explorer puts a source program beside the target code a compiler made from it and
links fragments of the two. This page describes a vertical slice of one whose links and claims
are Lean statements, each with a status decided from the Lean build:

* a **generic** Lean API (`Silmaril.Compiler.Explorer`): compilation problems over relational
  semantics with a backward refinement statement, segment mappings, segment disciplines, and the
  relations that the repository's institution semi-comorphisms generate;
* a **deterministic specialisation** (`Silmaril.Compiler.Explorer.Det`): machines
  `τ → Option τ`, the cut-point simulation of [compiles-to](compiles-to.md), and the theorem that
  connects them to the generic statement;
* the **C/x86-64 instance** (`Silmaril.Project.Shapes.CompilesTo.Explorer`) over the existing
  segment proofs, with problem shapes for `sil project`;
* the exporter `cexplorer-export`, the database and read-only API
  (`tools/compiler-explorer/cexplorer.py`) and the page (`tools/compiler-explorer/ui/`);
* fixtures in `examples/compiler-explorer/`. Compiled builds: the compiles-to objects and four
  staged programs. A decompiled block. An imported pair.

```mermaid
flowchart LR
  C["source (sha256)"] -->|"compiled: gcc 13.3.0, pinned image, receipt"| T["target (sha256)"]
  T -->|"decompiled: SemLift + WordC, receipt"| C
  C -.->|"debug info / decompiler block: navigation only"| T
  M["manifest: artifacts, derivation, models, ABI, relation, comorphism, fragments, edges, obligations"]
  M -->|"cexplorer-export, run by `verify`"| E["evidence"]
  P[("sil project database: rows, statuses")] -->|"`project` adapter: shape + arguments"| DB
  M --> DB[("explorer database")]
  E --> DB
  DB -->|"GET only"| UI["page"]
```

## The generic layer

| notion | Lean | meaning |
| --- | --- | --- |
| problem | `Problem σ τ R T` | source and target semantics (`Source`: relational steps, wrong states, final states with results), the entry relation (the ABI for code), the result relation |
| translation | `Problem.Refines` | from related entries with a safe source (no undefined behaviour, every run finite), the target is safe and finite, never stuck before a final state, and each target result is related to the result of some source run |
| non-vacuity | `Problem.Inhabited` | some related entry has a safe source |
| vertical composition | `Problem.comp`, `Problem.Refines.comp` | C → IR → machine; refinements compose when the middle semantics agree |
| mapping | `Mapping` | program points: the states at each point on each side, and the relation there (data) |
| coverage | `Mapping.Covers L` | no states are related at a point outside `L` |
| edge validity | `SegmentDiscipline` | a discipline says when an edge is valid and proves that valid edges compose into `Refines`; `all_of_listed` and `refines_of_listed` add coverage |
| relation refinement | `Mapping.RefinesAt G K` | the mapping's relation implies `G` at the points `K` |
| generated relations | `Gen.Agrees`, `Gen.Witnessed`, `Generator` | from a `Silmaril.Inst.SemiComorphism` and readings of states as models: entry, result and point relations |

**Direction.** `P.Refines` is a *backward* statement over **all** target runs, so it reads the
same for deterministic, nondeterministic and interleaving targets: the target's behaviours are
among the source's. `M.RefinesAt G K` says that the mapping's relation is at least as strong as
`G`. `Problem.Refines.mono`: a stronger entry relation and a weaker result relation keep a
refinement.

**Undefined behaviour, divergence, I/O, concurrency.**
* Source undefined behaviour permits every target behaviour. A divergent source run is not
  covered: `Source.Safe` includes termination.
* Source nondeterminism is handled because the target's result must be the result of *some*
  source run.
* I/O is what the result relation observes. There is no event trace.
* Concurrency fits the generic problem as an interleaving `Source`. No concurrent instance and no
  nondeterministic segment discipline exist yet. Replacing the x86 model with a multithreaded one
  needs that discipline, not a new problem type.

### Comorphisms, and what is generated

Relations come from the repository's **semi-comorphisms** (`Silmaril.Inst.SemiComorphism`,
`docs/projects/logic-inst.md`). They translate signatures and sentences forwards and models
backwards, with the satisfaction condition on a class of sentences, in the directions that hold.
States are not models: a reading maps a state to a model at a signature. Two generated relations
are defined:

* `Gen.Agrees f S readS readT Ψ s x`: each observed sentence holds of the source reading exactly
  when its translation holds of the target reading. Through the satisfaction condition this is
  agreement between the source reading and the model translation of the target reading
  (`Gen.agrees_iff_reduct`). Generated relations compose along `f ≫ˢ g` (`Gen.agrees_comp`).
* `Gen.Witnessed f S readS readT fam obs s x`: for each observed family, some instance holds on
  both sides. For value observations this means each observed object has a value that both sides
  hold (`Gen.witnessed_of_reduct`).

A `Generator` (one semi-comorphism, the entry, result and per-point signatures, the readings)
generates both kinds of relation:
* the compilation relations, as `Generator.problem`'s entry and result;
* the segment relations, as `Generator.mapping`'s point relation (a control relation and
  agreement).

`Generator.mapping_refines` is the specification of that construction, not a correctness result.
A mapping chosen by hand, such as the C instance's, is related to a generated relation only by a
separate refinement theorem.

`obsInst O V` is the institution of value observations: one signature, sentences `o = v`, models
the relations `O → V → Prop`. `obsSemi loc` is the semi-comorphism of an observable map `loc`.
Its satisfaction condition holds both ways on every sentence, and with one signature naturality
is trivial. It is the signature part of a debugger's location map, not a translation of
programs. No comorphism in the repository translates C states to x86 states (models are
valuations here, not states), so none is claimed.

## The deterministic specialisation

`DetProblem` is the earlier problem shape: a machine `τ → Option τ` whose return and result are
read relative to its entry state. Its fields are as follows.
* `DetProblem.Valid`: the machine reaches its **first** return (`DetProblem.Step` stops there).
* `DetProblem.toProblem`: the generic reading. Target states are (entry, current) pairs, and the
  machine stops at the first return.
* `DetProblem.refines_of_valid`: validity gives `Problem.Refines`. Determinism makes the one run
  the only run.
* `DetMapping` with `EdgeValid k := Corr.Segment k`.
* `DetMapping.refines_of_segments`: valid edges of a mapping that starts at the entry and relates
  no return give the refinement.
* `Det.discipline`: all of this as a `SegmentDiscipline`.

`Det.Counterexample.edges_not_enough` is a mapping whose one listed edge is valid and whose
points are not covered, with neither `Valid` nor `Refines`. Individually valid links prove
neither the mapping nor the translation.

## The C/x86-64 instance

`FnData.compilation I k0` is the deterministic problem of a function. Its source is the Cerberus
Core run of the procedure. Its target is the model `I` running the function's bytes. Its entry is
the System V call. Its result is the System V return: callee-saved registers restored, writes
only in the frame, and the value in `rax`.

| theorem | statement |
| --- | --- |
| `FnData.compilation_refines_of_segments` | every proved segment gives `(F.compilation I k0).toProblem.Refines`, for every caller continuation |
| `FnData.compilation_inhabited` | not vacuous: for the empty caller continuation, a canonical Core entry that is safe and a System V entry the placement admits are related |
| `FnData.refines_dwarf` | for every function, the mapping refines the relation generated by the location semi-comorphism `dwarf = obsSemi (o ↦ (o.off, o.size))` |

`readCore` reads a Core state as a valuation of C objects: the object's symbol is bound to an
allocation whose `int` slot holds `n` (`Locals.Slot`). `readFrame` reads a machine state as a
valuation of frame slots (`DW_OP_fbreg`, frame base the CFA). The refinement goes from the
verified Core library's invariant (`StateMem.Inv`) to Core's own reading of the object. The
theorem says less than it might seem to:
* The slot offsets are the `FnData`'s. `tools/c-tv` read them from DWARF with an unverified
  reader, and no statement says they are the object's DWARF locations.
* It is close to the definition of the relation, because `ObjectsAgree` is part of it.
* It gives *a* common value, not equality of every read: a slot fixes four bytes, not an integer.

## Segment relations in the page

There are two kinds of link, never mixed:

* **Navigation links**: the line table read by `tools/c-tv`, the `.loc` directives of `gcc -S`
  (as Compiler Explorer reads them), or a decompiler's input block. They say where code came
  from, and carry no obligation.
* **Semantic links**: the program points of a Lean mapping. The source fragment is the
  statement's lines (`PointOf F k line`, proved). The target fragment is where the segment starts,
  laid out up to the next point. The proof is about the run, which may jump.

| phenomenon | where |
| --- | --- |
| one line, several discontiguous instruction ranges | `msort.c -O2`, line 8 (inside the inlined `merge`) |
| one line, copies in several functions (duplication) | `lisp.c -O2`: `cons` and `mk` inlined into `read` and `eval` |
| a call with no code of its own (inlining, elimination) | `msort.c -O2`, line 24 (`merge(…)`) |
| instructions from another file | `lisp.c -O2`: `putchar` from `bits/stdio.h` |
| generated code (prologue, argument spills) | `-O0`: attributed to the opening brace |
| no statement-level point | every `-O2` object: c-tv's reason is shown on the link |
| uncovered source, uncovered target | the page's footer; the decompiled block excludes `ret` |

**Fragments** are sets of ranges in one artifact's coordinate space, identified by
`sha256(artifact sha256 : space : ranges)`.

## Directions and provenance

| direction | what is checked on ingest | fixture |
| --- | --- | --- |
| compiled | the compiler's receipt read the source bytes and wrote the target bytes, in the recorded image | `examples/compiles-to`, `programs/` |
| decompiled | the decompiler's receipt read the target bytes and wrote the source bytes | `decompiled/scale`: gcc 13.3.0 `-O2` of `scale.c`, decompiled by `SemLift.propose`, `SemLift.check` (which accepts the proposal) and `WordC.regenerate` into `wc_scale` |
| imported | nothing is derived; an origin may only be recorded as a claim | `imported/sha256-compress`: `xc_sha256.c` and the clang `-O2` assembly of `apps/sha256-cli` |

The decompiled fixture has one stated obligation, `decompilation`:
`Silmaril.Compiler.Explorer.DecompiledBlock "scale" bytes 1 inputs source`
(`Silmaril.Compiler.Explorer.Decompiled`). It says three things:
* the proposer's summary of the block is accepted by `SemLift.check`;
* its `rax` expression lowers to a term that prints as exactly the text of `scale.dec.c`;
* from every state where the block is loaded and entered, the machine reaches a state whose
  `rax` is the C0 value of that term's typed Ail (`WordC.checked_output_c0`, through the generic
  `decompiledBlock_of`).

`CompilesToExamples.Explorer.Decompiled.scale` proves it for the five bytes, by kernel evaluation.
Its statement is built from the fixture's own data:
* the source artifact's text, as a Lean string literal;
* the block's bytes. On ingest, the database reads the object's `.text` section from the ELF file
  and checks that the bytes are there at the receipt's range. That is a tool check, not the
  kernel's.

What is not stated, and why:
* The C text is *printed from* the term. It is not parsed or elaborated back, so no Cerberus or
  C0 reading of the text itself is involved.
* `ret` and the System V convention lie outside the block.
* C0 is the repository's C subset interpreter, not Cerberus.

So the translation, ABI, mapping and refinement questions stay unsupported for this problem. The imported assembly has a functional contract against a SHA-256
specification (`Sha256O2.sha256_compress_O2`, [sha256sum](sha256sum.md)). That contract is not a
statement about the C source beside it.

## Evidence, statuses and trust

A status comes from one of three origins. Only the first two can make an obligation proved.

| origin | how | counts as proved |
| --- | --- | --- |
| `exporter-run` | `cexplorer.py verify` runs `cexplorer-export` on the manifest. The exporter needs a theorem whose type is the obligation's statement (up to reducible unfolding), with the standard axioms. | yes |
| `sil-project` | `cexplorer.py project DB project.sqlite` reads the obligation's row. The row must be an instance of the kind's shape (`ROW_SHAPES`) with the manifest's arguments, have a THM status at tier `kernel`, and its theorem must use the standard axioms. | yes |
| `file` | `cexplorer.py evidence` records an exporter file someone handed in | no: shown as **claimed** |

| status | meaning |
| --- | --- |
| proved | as above, for this manifest version |
| unbound | proved, but the artifact obligation (the function's bytes are the registered object's code) is not proved |
| claimed | a handed-in exporter file says kernel |
| open | stated, no proof named or the row is open |
| unchecked | a proof is named, no result recorded |
| rejected | the named proof is missing, not a theorem, about another statement, or has other axioms; or the row is of another shape or function |
| stale | proved for another version of the problem only; evidence never moves between versions |
| unsupported | not stated: no model covers it (with the reason) |

**What the checks do.**
* Ingest re-reads and re-hashes every artifact. Symbolic links out of the repository are
  refused.
* Statements are templates per obligation kind, over Lean names that must be identifiers. The
  model and comorphism names must be the context's, and the target value must read the
  registered target artifact.
* A compiled problem needs a receipt about its exact bytes.
* Tests are stored apart from evidence, and an execution test never proves an obligation.

**What each link rests on.** Each line below is shown in the page.
* Kernel:
  - every obligation shown proved;
  - the binding of the function's bytes to the registered object (artifact obligation).
* Not checked by the kernel:
  - Evaluation (`#guard`): C text → typed Ail.
  - Unverified: the line table and slot offsets read by `tools/c-tv`.
  - Recorded only: receipts (compiler, version, image digest, hashes).
  - Trusted: the semantics themselves (the Lean port of Cerberus Core, `Silmaril.X86.Open.isa`).
  - Replay boundary: the exporter reads theorem types from `.olean` files. `replay.sh` (run by
    `make compiler-explorer-check`) re-runs the toolchain's `leanchecker` on the evidence modules:
    - each module's own declarations go through the kernel again, on top of imports loaded from
      their `.olean` files;
    - the imports themselves are not replayed (no `--fresh`, which would include Mathlib);
    - it is the same kernel as the build, not an independent checker.

    Locally, all 9 modules replay in 16–19 s each (`leanchecker-paranoid` on `Builds`: same
    result).

**Conditional and unconditional.**
* The translation holds from every related entry whose Core state is safe: no Core run from it
  reaches undefined behaviour, and every Core run from it is finite. From any other entry it says
  nothing.
* `c.compiles_to` (every Core entry, through `Task.<f>_safe`) remains open.
* Non-vacuity is shown for one entry.
* "ABI" means that an entry state exists for every argument tuple. Every execution's return-side
  ABI is part of the translation.

## Database

The schema is at version 3 (`schema_migrations`). Migration 2 records the origin of evidence;
migration 3 records the `sil project` row of each obligation. Tests migrate a version-1 database
with its data.

The tables:
* `artifacts`: bytes by SHA-256, insert-only.
* `problem_versions`: one per manifest, with direction, derivation, models, ABI, relation,
  comorphism and a context hash.
* `fragments`, `edges`, `edge_ends`: the many-to-many mapping.
* `obligations`, `evidence`, `tests`.
* `rejections`: every refused manifest, evidence file or project database, with the reason.

The server opens the database read-only and answers GET only. It has no endpoint that compiles
or runs anything, and it sets a restrictive Content-Security-Policy. The page inserts every text
with `textContent`.

## `sil project` and the Pages explorer

The explorer's obligations of the compiles-to builds are rows of the project
(`silmaril/compiler-explorer.toml`, group `silmaril.compiler_explorer.all`, a child of
`silmaril.all`). They are instances of six shapes, `silmaril.shapes.compiler_explorer.c.*` (including `code`, the binding of the function to its object), and
are solved in `CompilesToExamples.Explorer.Rows`. `sil project dump`, `sqlite` and `explore`
therefore record their statuses and show them on the published explorer like every other row.

The adapter boundary is the project database schema `silmaril.project-db.v0.1`:
* `problems.name` is the row;
* `edges(kind = 'instance', parent → child)` gives the shape;
* `instance_args(problem, pos, term)` gives the arguments;
* `statuses(problem, status = 'THM', tier = 'kernel', via)` gives the solving theorem;
* `answer_axioms(decl, axiom)` gives its axioms.

The adapter refuses another schema. The source↔target view itself is not a tab of the Pages
explorer yet. That needs the manifests and artifact bytes in what Pages serves, and a view
registered in `tools/silmaril-project/src/project/explore.rs`. Both sit on files the open C TV
(#900, #934) and assembly-tab (#890) pull requests change. The obligations are already in the
database; a tab would read this page's API shape (`problem_view`) from a static export.

## Fixtures and results

`tools/compiler-explorer/check.sh` (`make compiler-explorer-check`) writes the statuses and
compares them with `examples/compiler-explorer/expected-status.txt`:

| problem | translation | non-vacuity | ABI entry | mapping | links | location refinement |
| --- | --- | --- | --- | --- | --- | --- |
| `straight.c -O0 add3` | proved | proved | proved | proved | 5/5 | proved |
| `straight.c -O2 add3` | proved | proved | proved | proved | 1/1 | proved |
| `branch.c -O0 max2` | proved | proved | proved | proved | 5/5 | proved |
| `branch.c -O2 max2` | open | proved | proved | open | 0/1 | proved |
| `loop.c sum_to` | unsupported: the elaborator has no `while` | | | | | |
| `hello`, `msort`, `fft`, `lisp` | unsupported (execution tests against expected output: passed) | | | | debug info only | |
| `decompiled/scale` | unsupported; the `decompilation` obligation (block → C0) is proved | | | | the decompiled block | |
| `imported/sha256-compress` | unsupported | | | | none | |

The other obligations are proved for every row with statements: the C-to-Core points, the
elaboration, the binding of the function's bytes to the registered object, and the
canonical-entry row. Safety from every Core entry is open everywhere.

## Acceptance

| requirement | state |
| --- | --- |
| generic problem and segment relations, independent of determinism | done: `Problem`, `Mapping`, `SegmentDiscipline`; determinism is `Det` |
| comorphism-generated compilation and segment relations, separate refinement theorem | done on `SemiComorphism` (`Generator`, `Agrees`, `Witnessed`); `FnData.refines_dwarf` |
| refinement direction, UB, divergence, nondeterminism, concurrency | stated (above, `Defs`) |
| per-edge vs whole mapping, coverage, counterexample | done (`Det.Counterexample.edges_not_enough`) |
| non-vacuity | done for the C instance (`compilation_inhabited`) |
| CI | done: `make check` runs the database and view tests, and `compiler-explorer-check` when `cexplorer-export` or `CompilesToExamples` is in scope; a broken proof fails it |
| `sil project` | done: shapes, rows and the database adapter; the Pages tab is the remaining step (above) |
| decompiled and imported directions | done, with fixtures; the decompiled block's machine → C0 obligation is proved (bound to the object's bytes by a tool check, to the C text by printing); no whole-function decompilation theorem |
| kernel replay | `leanchecker` on the evidence modules in `make compiler-explorer-check` (imports from `.olean`, same kernel) |
| nondeterministic segment discipline, concurrent target | not done |
| interactive compilation (choose compiler, flags, source; compile on demand) | not done: a remaining goal. It needs a sandboxed compile service (resource limits, no network, pinned images, receipts written by the service) with an API the database can trust; the repository has none, and this page must not run compilers itself |

## Build

```sh
tools/compiler-explorer/check.sh                 # or: make compiler-explorer-check
python3 -I tools/compiler-explorer/cexplorer.py serve .lake/compiler-explorer/explorer.sqlite
python3 -I tools/compiler-explorer/fixtures.py build|listings|decompile   # Docker (and Lean)
python3 -I tools/compiler-explorer/fixtures.py manifests|rows             # deterministic
```
