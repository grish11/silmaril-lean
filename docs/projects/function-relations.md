# Function relations and call graphs

This API follows the [region abstraction](region-extraction.md). A function row
proposed from a byte window, a valid first-exit body, an edge in a possible call
graph, and a witnessed execution are different judgments.

| Layer | Lean entry point | Contract |
| --- | --- | --- |
| Relations | `Silmaril.Semantics.Function.Thms` | Source-qualified body, node, and call atoms; graph queries; raw and lawful models |
| Interpretation | `Silmaril.Semantics.Function.Semantic.Thms` | Steps, ownership, call events and conventions; correspondence for CFG bodies and observations |
| Effects | `Silmaril.Semantics.Function.Effects.Thms` | Indexed bounds, state-threaded composition, and region WP |
| Institution | `Silmaril.Logic.Function.Thms` | Typed signature renaming into the existing atomic `Room` institution |
| Object extraction | `Silmaril.Elf.Region.Calls.Thms` | Declared ELF windows, call findings, checked partition wrapper and finite direct queries |
| General queries | `Silmaril.Elf.Region.Calls.General.Thms` | Executable mixed direct/indirect paths and foreign frontier; reachable uncertainty stays explicit |
| Symbol input | `Silmaril.Elf.Region.Calls.Symbols.Defs` | Candidate function windows from one selected ELF symbol table; foreign bindings remain declared |
| x86 interpretation | `Silmaril.Elf.Region.Calls.Semantic.Thms` | Retiring direct `CALL` steps in the `Ext` profile, conditional on placement/site coverage |

## Rows and laws

`Decomposition` assigns zero or more opaque rows to each internal identity.
`fromRegionView` projects a region relation through an abstract CFG entry and
exit interface; it does not classify those exits. Coverage and unique ownership
are independent predicates, not inherent in the rows. A partition of addresses
also needs disjoint rows, not just unique owners if an owner has multiple rows.

At a fixed signature, the raw lattice is the Region `RawModel` powerset. The
lawful lattice uses the Region positive closure (`ClosedModel`); intersections
give meets and closure of unions gives joins. Its only rules say that a body
implies its internal node, and a call implies its caller and callee nodes.
Complements, exactness, coverage and semantic validity are not closure rules.
An absent atom is not a certificate that the corresponding event cannot occur.

An internal identifier and a foreign label belong to different node types.
Foreign nodes are leaves in this graph: a foreign implementation, callbacks,
effects and return behavior require a separate interface. Transfer kind
(`invoke`/`tail`) is independent of dispatch (`direct`/`indirect`). `Room` here
is the existing categorical room of sentences and models, not a CFG component:
renaming preserves node kinds and transfer/dispatch tags, sends sentences
forward, and pulls models back. Membership gives satisfaction in both rooms;
the reduct of a presence-closed model preserves the laws. Renaming need not be
injective, so this is not a claim that it reflects uniqueness or path feasibility.

## Interpreting a model

Supply `Machine` with a transition system, an ownership predicate, an event
classifier, and invocation, return and tail-transfer conventions. The
classification of a call is tied to a real step and both its states. Supply
`Boundaries` with an abstract `Graph.CFGLike` view, entry admission and
well-formed labels. `Correspondence` requires a valid region with an inhabited
entry, a first-exit support/exit proof, real return or call-transfer obligations,
and a coverage proof for each admitted call step. It gives inclusion of proposed
bodies in semantic bodies and coverage of actual events by the may relation.
It does not assert termination, support completeness or a full ABI.

`Silmaril.Semantics.Function.Examples.Thms` proves these obligations for a
two-state event model. `Silmaril.Elf.Region.Calls.Examples.Thms` reuses the same
`body_sound`, `may_cover`, and `consecutive_path` scheme for loaded x86 bytes.
Its revised x86 interpretation changes the designated return address and
strengthens ownership with a PC check. Its adapter re-establishes coverage and
retirements; no changes are needed to atoms, path APIs, or the generic theorems.
`scripts/check-function-imports.py`, run by the layout check, enforces the
transitive Silmaril import boundary.

## ELF contract and graph queries

The caller declares stub address-to-foreign-label bindings and known tail sites.
Function windows can be supplied directly or derived by `readSymbolPlan` from
one selected `.symtab` or `.dynsym`, using the existing staged layout and symbol
readers on the same bytes. The reader accepts x86-64 `ET_EXEC`/`ET_DYN` and
keeps nonempty `STT_FUNC` extents contained in file-backed executable sections;
it neither resolves IFUNCs nor deduplicates aliases. The object wrapper reads only uniquely mapped,
file-backed executable virtual addresses supplied by `PT_LOAD` records.
Section-relative objects, zero-fill, load bias, relocation, overlapping
mappings, dynamic symbol resolution and executable-memory preservation are not
inferred. A readable row certifies declared source bytes; `checkPartition` uses
the existing x86 partition checker for stronger window claims. Neither one
implies a semantic function body. `FindingAt` ties a finding to a scan of the
declared source window. This decoder scan is not an execution and can include
unreachable instructions. Duplicate local entries or colliding stub declarations
are unresolved, not silently disambiguated. A declared stub edge means a
transfer to its stub address under that interface, not execution of the named
foreign function.

The direct-only runner reports partial results on fuel exhaustion, unsupported
instructions, unclassified exits, missing rows, unresolved direct calls and
observed indirect transfers. A stable finite projection certifies reachable
nodes, nonempty direct paths (with a separate seed), reachable caller/callee
pairs and the foreign frontier **of the extracted direct graph**. Graph calls
retain source sites in the relation; the finite report of arcs forgets them.
The root is reflexively reachable, not necessarily reachable by a nonempty
call path. Truth of a path in the may graph is not a must-call property or an
execution witness: adjacent edges may require incompatible states.
`Consecutive` instead shares concrete intermediate states and projects to the
may graph under coverage. Intervening instructions would require an additional
stepping rule.

The scanner recognizes the particular indirect observations `FF D0` (call) and
`FF E0` (jump, a tail edge only if declared). Unsupported encodings are gaps,
not proof of the absence of calls. `queryGeneral` follows direct edges and the
listed targets of observed indirect sites. `finitePaths` computes endpoints
of nonempty paths, while `finiteReach` includes the root. A checked fixed point
is exact for the known finite graph, and a report without issues is exact for
the full **declared** analysis reachable from the root. The direct graph embeds
in the finite graph. `declared_mono` proves that widening target bounds preserves
may paths. Replacing a list by Top may drop enumerated witnesses while still
enlarging the declared may relation.

The general report records reachable Top sites, scan gaps, missing or ambiguous
rows, and exhausted fuel. In those cases it retains known witnesses but returns
a conservative Top frontier bound that admits even undeclared foreign identities.
An unreachable Top site does not open a report from another root. `none` means
all typed targets; a known empty list means none. An empty known frontier with
an open bound does **not** prove absence of foreign calls. For an operational
reachable-call bound, a separate `CallGraphProblem` certificate must cover the
actual call events, including the declared finite bounds at indirect sites.

`extModel` describes only admitted direct transfers that retire with the
required stack write. Its proof uses executable fetch, the existing decoder and
the `Ext` transition system. It does not prove general `CALL`/`RET` pairing,
indirect or tail execution, dynamic loading, arbitrary continuation after a
call, or foreign execution. In particular the corpus fixture has no operational
claim. The region/extraction and state/site correspondence obligations remain
explicit for new images and for other interpreters.

## Indexed effects

`OnArgs`, `OnEntry`, and `OnResult` are one family indexed by symbolic arguments,
entry state, or `(Args, Result)`. Sound summaries upper-bound observations for
each index; the least summary is the pointwise join of those observations.
`abstractInput_sound` requires an upper bound for every represented concrete
input, not a chosen representative. Memory belongs to the instantiation: the
two-state example uses a symbolic memory bit, and the x86 example constrains a
caller and optionally its stack pointer while bounding retired-call targets.
The two-state example also checks that a wrong argument/result pair has no
observation. `ExitSound` agrees with region partial Hoare/WP, including
separate halt obligations. `sequence` composes relational summaries on a shared
intermediate state and is monotone under inclusion. Joining per-input effects
without retaining that correlation can still upper-bound possible observations,
but cannot justify an input-dependent path as feasible.

## Reproduce the checks

```sh
make check CHECK_TARGETS='Silmaril.Elf.Region.Calls.Examples.Thms Silmaril.Semantics.Function.Examples.Thms Silmaril.Logic.Function.Thms'
```

| Fixture | Checked scope |
| --- | --- |
| Synthetic x86 | 13 code bytes, three partition claims, two actual call retirements (`0 → 6 → 12`) and one declared foreign leaf; the direct frontier stabilizes within three rounds |
| Mixed x86 candidates | 13 code bytes; bounded indirect `0 → 3` then direct `3 → 9` to a declared foreign stub. Top at `10` is unreachable until widening adds `0 → 10`; reachability then stays open while retaining the known stub. The path has no consecutive witness from the tested `Ext` entry state |
| Pinned `hello-gcc` | 27-byte `main` window in the existing 15,960-byte fixture, one direct candidate `main → puts@plt`, foreign label declared. Reading symbol table 28 derives two function windows; no loader or execution theorem for this edge |
| Negatives | Open report on zero fuel, a recognized indirect call, an unsupported opcode, an ambiguous entry, an unclassified jump and fallthrough outside the row; adding a tail declaration exposes a tail candidate only |

Pinned `hello-gcc` SHA-256:
`6964f3f23e27cfd2b6c26bd469cb210ff000dd359fc9988138cadc96683065c7`.
These are fixture counts, not whole-corpus coverage or a timing benchmark.
