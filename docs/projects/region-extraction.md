# Region extraction: relations, first exits and candidates

This framework adds abstract region judgments and semantic interpretations
independently of function extraction. Fixed-signature raw and positive-rule
lawful models form complete lattices; see the
[abstract lattice API and proofs](region-lattices.md) and the
[tree/CFG variants and dominance bridge](region-trees.md). A region can be certified
through a state invariant even when an unrestricted constituent block cannot. It does not infer a unique partition,
prove an arbitrary parent region, or manufacture call resumptions.

## Reading and building

The public entry points are:

| Layer | Definitions and theorem header | Main result |
| --- | --- | --- |
| Abstract lattice | `Silmaril.Semantics.Region.Abstract.{Defs,Thms}`, `Abstract.Named.Thms` | Arbitrary typed atoms, fixed positive rules, raw/lawful complete lattices and fixed ceilings |
| Tree/CFG variants | `Silmaril.Semantics.Region.Tree.{Thms,CFG.Thms,Finite.Thms}`, `Silmaril.Automata.Graph.RegionTree.Thms` | Primitive tree relations, annotation/flat projections, separate successor adjacency, conditional and witnessed lifting |
| Raw relations | `Silmaril.Semantics.Region.{Defs,Thms}` | Independent signatures, lawful coherence, erasure and context equivalences |
| Semantics | `Silmaril.Semantics.Region.Semantic.{Defs,Thms}` | First exits, greatest sound judgments, gluing, queries and WP |
| Counterexamples | `Silmaril.Semantics.Region.Examples.Thms` | Invariant-restricted indirect transfer, divergence, incompatible erasure witnesses |
| Binary layout | `Silmaril.Machine.Region.{Defs,Thms}` | Typed coordinates, sparse byte sources, unambiguous translation |
| x86 | `Silmaril.Machine.Region.X86.{Defs,Thms}` | Existing Ext retirement semantics and decoded-listing soundness |
| Concrete fixtures | `Silmaril.Machine.Region.Examples.Thms` | Nonvacuous loaded direct-branch certificate and classification checks |
| ELF | `Silmaril.Elf.Region.Defs` | Executable file-backed PT_LOAD and section-relative mapping |
| Loaded images | `Silmaril.Process.Region.Defs` | Existing LPS image and permission-checked sparse memory adapters |
| Wasm | `Silmaril.Wasm.Region.{Defs,Thms}` | Existing block inventory, conservative candidates, validated byte-map interface |
| Logic | `Silmaril.Logic.Region.{Defs,Thms}` | Raw-relation signature category and institution |

Run with the repository's pinned toolchain and dependency manifest:

```sh
lake build --wfail \
  Silmaril.Semantics.Region.Tree.Examples.Thms \
  Silmaril.Automata.Graph.RegionTree.Examples.Thms \
  Silmaril.Semantics.Region.Abstract.Examples.Thms \
  Silmaril.Semantics.Region.Examples.Thms \
  Silmaril.Machine.Region.Examples.Thms \
  Silmaril.Wasm.Region.Thms Silmaril.Elf.Region.Defs \
  Silmaril.Process.Region.Defs Silmaril.Logic.Region.Thms
```

The same targets can be passed as `CHECK_TARGETS` to `make check` to run the
source/regression gates along with the targeted Lean build. Unscoped
`make check` also builds the whole library and native tools; targeted success
must not be reported as a full native release check.

## The raw vocabulary and its laws

The totally abstract named API additionally takes independent `Support` and
`Exits` carriers, with no collection operations. The signatures below are the
existing finite-set profile, now aliases of that API.

The carriers are `Img`, `Assum` (the specification's interface carrier `Int`,
not Lean's integer type), `Seg`, and `Lab`. The individual predicate aliases
are usable without a record. `SegmentRegionModel` bundles all five:

```
SegBB : Img → Assum → Seg → Prop
BB    : Img → Assum → Seg → Lab → Finset Lab → Prop
SR    : Img → Assum → Finset Seg → Lab → Lab → Prop
SR'   : Img → Assum → Finset Seg → Lab → Option Lab → Prop
Reg   : Img → Assum → Finset Seg → Lab → Finset Lab → Prop
```

Raw predicates have no automatic semantic guarantees. `SegmentRegionLaws`
separately requires BB to imply SegBB and singleton-support Reg. SR is exactly
Reg with a singleton declared exit; SR' is exactly Reg with the option's zero
or one labels. Thus BB with one exit embeds into SR. `ofReg` derives coherent
SR/SR' predicates instead of duplicating certification obligations.

`SR` means exactly one *declared* normal exit. It does not assert that the
exit is reached, or that there is only one possible abnormal outcome.
`Exact` supplies the separate, stronger reachable-exit interpretation.
In this profile, collections and exits are finite sets, with no order dependency.
Individual segments can retain ordered byte/instruction ranges. `ListRow` is an ordered
serialization adapter whose certification uses `toFinset`, so duplicate or
reordered presentation labels cannot change validity. `CertifiedSegmentRow`,
`CertifiedRow`, and `CertifiedListRow` fix the image and interface and keep
candidate data distinct from its certificate. This is an API for future
exporters, not a new viewer or an ELF corpus extraction tool.

## Semantic validity and observations

`TransitionSystem` supplies a PC, effect-labelled steps, and distinguished
halts. State contains memory, registers, stack, guards and frame/interface
state. The effect and halt alphabets are parameters: a client can observe
syscalls, foreign calls and UB as events, and distinguish return, trap, raise,
stuckness and exhaustion as appropriate. The client must document its policy.
The generic system permits nondeterminism and does not assume halt/step
exclusivity; adapters should prove it when their operational model requires it.

`FirstExit T U s trace t` is a **nonempty finite execution** whose source
states stay in support U and whose final state is the first outside U. Normal
exits need not be terminal: execution may continue or reenter afterwards.
`Inside` includes the empty internal prefix. `Sound` quantifies over every
first exit from an explicit admitted domain. `Valid` also requires a
well-formed entry in support, well-formed declared exits, an inhabited admitted
domain, and entry-PC agreement. Internal label validity is the responsibility
of the support interpretation and operational adapter; only boundary labels
are checked by `Valid`'s `wf` predicate. Empty raw supports are representable,
but cannot satisfy this semantic entry convention.

An empty exit allowance excludes normal first exits only. A region may loop,
halt, trap, raise or get stuck. The loop fixture proves both soundness with
empty exits and divergence. `ReachableExit`, `MayEffect`, `Stuck`, and
`Diverges` expose these questions separately. `PartialHoare` has label-indexed
normal postconditions and halt-indexed abnormal/return postconditions, both
receiving trace and final state. `SinglePost` specializes normal postconditions
to one label. `TotalHoare` adds accessibility of the internal transition
relation and progress at every reachable internal state; it rules out
internal divergence (`finishes_not_diverges`) and stuckness. It does not mean
"returns normally" unless the halt postconditions require that policy.
`wp_iff` characterizes demonic partial WP; `wp_unfold` composes through a real
step, passing its trace prefix and state to the continuation.

For fixed semantics, admitted domain, label validity and support interpretation,
`greatest` is the greatest relation of valid region rows.
`recognizer_included` proves every sound recognizer is included. `outward` is
the set of actually reachable first-exit labels; `sound_iff_outward` says it
is contained in every sound allowance. These are different extremal objects:
the greatest **set of sound rows**, and the least **sound successor allowance**.
Neither need be computable; the latter need not be finite. `exact_unique`
proves equality of exact exit predicates for the same context. None of this
selects a unique maximal partition.

## Gluing, entry domains and weakening

`Local` certifies a state invariant's preservation while staying inside a
child, and a state predicate on every crossing. `Wiring` requires actual
crossings into the other support to establish that child's entry PC **and**
admitted invariant. Actual outward transfers must satisfy the parent allowance.
`glue_local` and `glue_sound` prove closure for disjoint two-child supports;
they permit backedges. A sequential plug is the case where the second child
has no transfer back into the first. The same T fixes the image, interface,
frame and effect policy; changes to any of these need a separate simulation
or compatibility proof. No hidden stability of code memory is assumed.

`FamilyWiring`/`family_sound` generalize to a family, in particular `Fin n`
for finite graph glue. They allow overlapping supports only when every actual
crossing establishes a compatible destination domain. Outward edges come
from actual steps outside the union, never blind subtraction of an internal
label from the declared exits. This also covers loops and edges returning to
a group's own head. `singleEntry_union` separately proves structural entry
closure when all external entries into the second support originate in the
first. Arbitrary parents and arbitrary cross-boundary entries are not covered.

The indirect-transfer fixture first sets a selector to true, then dispatches
through it. The whole region has normal exit 2. Its inner block, entered with
an arbitrary selector, can instead exit at 3 and fails local certification.
Restricting that block's entry domain restores soundness. This is a semantic
counterexample to defining all valid regions solely as partitions into blocks
valid under their original local domains.

`sound_weaken` permits a smaller admitted domain and larger exit allowance for
fixed T and support. This does not transport across an assumption-dependent
change of semantics or entry validity. An empty admitted domain invalidates
`Valid`'s nonvacuity requirement; restricting a domain can remove an exact
exit, and enlarging an allowance can introduce an unreachable label. Exact
exit validity therefore has no such general weakening rule.

Composition does not construct a dominator tree. That additionally needs a
chosen graph, edge coverage from execution (and any converse needed for an
exact claim), a root/admitted entry set, reachability, and the appropriate
single-entry constraints. Reuse the existing
[`Automata.Graph`](../../Silmaril/Automata/Graph/Defs.lean) dominance and region
tree APIs, which distinguish sound trees, exact dominator trees and nonunique
region bracketings. This framework does not reimplement them.

## Forgetting, contexts and the institution

`RegionModel` has only the label judgment. Erasure existentially quantifies
support for Reg, BB, SR and SR'; their lawful implications are preserved.
SegBB erasure is an **unlabelled** existential proposition. Acquiring a
labelled boundary requires a BB witness (`erase_with_boundary`); SegBB itself
never carried one. `erased_incompatible` proves that independent existential
witnesses need not be compatible. `erase_glue` consequently transports a
specified gluing law only when compatible witnesses exist.

Both model records have genuine curry/uncurry equivalences for `(Img, Assum)`
contexts, with inverse equations; predicates have corresponding equations.
Laws and erasure transport across uncurry. Helpers have a context adapter.
Optional helpers allow partial image-independent entry lookup, exits by
segment or entry+segment, and an abstract terminator. `Targets.top` always
soundly overapproximates label targets. It is not evidence of finite closure.
Missing/unknown terminators are not an empty set. `terminator_sound` explicitly
requires coverage of **every first exit**, including possible side exits,
before a terminator's target certificate can establish region soundness.

The implemented institution has four-carrier signatures and arbitrary name
maps, ground raw judgments plus Boolean connectives as sentences, arbitrary
raw bundles as models, and pi-style precomposition as reduct. Finite support
and exit sets translate by image. Identity/composition, satisfaction and law
transport are proved. Models form a discrete category. Existential erasure
is not claimed to be a sentence translation: a reduct may lose witnesses.
Arbitrary binary encodings and gluing operations are not claimed to be
categorical. See the existing
[institution API and references](../../Silmaril/Logic/Institution/Basic.lean).

## Concrete adapter boundaries and pending gates

* **ByteArray and kernel memory.** `ByteSource.ofByteArray` and `ofKBytes` use
  the existing `KBytes` reader; no public carrier named `KMem` was found in
  this checkout. `ByteSource.read` also accepts arbitrary sparse kernel-memory
  readers without imposing ELF. Layout translation rejects multiple owners.
* **ELF.** Reuses `Formats.ELF` record types/readers, mapping only executable
  file-backed PT_LOAD bytes or explicit section-relative code. It does not
  infer relocation effects, function boundaries, or resumptions. Existing
  `Elf.Parses`, `Staged.LayoutIs`, code facts and loader certificates remain
  the authority relating metadata to bytes/execution; this PR does not prove
  a new end-to-end ELF-loader-to-region theorem.
* **Loaded images.** Uses existing `Process.LPS.Image` segments and
  `Process.Memory.fetchBytes` permission checks. Optional omitted data imposes
  no value constraints, so semantics must quantify over compatible concrete
  completions; missing bytes never become zeros. Code-placement/permission
  compatibility still needs the ISA adapter's load invariant.
* **x86.** `system` is the actual handwritten `X86.Ext.step`, with its existing
  designated-return policy. It emits no events (`Empty`); Ext has no syscall
  instruction. Every non-retirement is a distinguished halt, with no synthetic
  fallthrough for calls. `instruction_sound` reuses `Decoded.edges_sound`;
  `listing_step` reuses decode/load/retirement facts. `listing_sound` requires
  preservation of the code-load and state invariant at internal successors.
  A concrete loaded `EB 00` fixture proves a nonvacuous valid region. Calls
  and returns produce Top for candidate targets; unsupported/truncated bytes
  fail decoding. General indirect x86 dispatch and call-summary integration
  need an operational semantics and summary soundness proofs, not guesses.
  `greatestRows` instantiates the greatest semantic relation for fixed Ext
  context; this is not a hardware correspondence theorem.
* **Wasm.** Reuses `Cfg.blocks`, `lookup`, `succOf`, `effectSucc` and effect
  marks. Structured synthetic exit/trap/raise/invalid labels remain distinct.
  Calls and unresolved handlers produce Top. `candidate_covers` preserves
  existing syntactic edges, and deliberately claims no operational coverage.
  Decoded labels contain function index, nested sequence path and instruction
  offset; raw labels contain function index and body byte offset. The
  `ValidatedByteMap` interface requires real decode/encoding correspondence,
  bounds and uniqueness. Producing a complete map from the binary decoder,
  proving its coverage, and connecting candidate CFG rows to the existing
  `Cfg.Region`/`Cfg.Session` operational theorems remain gates. No second
  Wasm extraction or execution implementation is introduced. See
  [the existing CFG guide](wasm-cfg.md).

## Fixture coverage

`classification_report` is a kernel-checked measurement over **seven
byte strings in `fixtureCorpus`**, not the existing 54-ELF corpus. All seven
match the expected finite/Top classification; five have finite normal targets
(two direct jumps, a conditional branch, NOP, UD2), and two are deliberately
Top (CALL, RET). This is classification coverage, not seven certified regions.
The direct `EB 00` region is the concrete semantic certificate. Separate
negative checks cover a truncated branch, unsupported opcode, ambiguous
mapping and section/VA mismatch. No canonical ELF corpus run or corpus-wide
coverage result is claimed.
