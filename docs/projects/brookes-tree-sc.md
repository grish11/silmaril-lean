# Brookes raw tree–SC comparison

Import `Silmaril.Semantics.Brookes.TreeSC.Thms`. C3 compares finite
store-aware observations of a read/write component with the existing Track A
sequential-consistency (SC) machine. The overlap is `Program Empty R`, with
both access modes, reply-dependent loads, and immediate writes. Locations
have decidable equality and stores are total functions `R → Nat`. An empty
lock type excludes both mutex commands. The comparison uses raw SC, so it
includes executions that a separate race policy may reject.
[Definitions](../../Silmaril/Semantics/Brookes/TreeSC/Defs.lean)
[Theorems](../../Silmaril/Semantics/Brookes/TreeSC/Thms.lean)

## Observations and scope

A `Frame` records a typed request and its actual reply, plus the stores
immediately before and after the primitive. Reads return the value from the
pre-store and preserve it. Writes return unit and update the addressed cell.
`Frame.event` supplies a thread identity and projects to Track A's event
type. `StoreFollows gap` requires the supplied relation from the initial
store to the first pre-store and from each preceding post-store to the next
pre-store. The endpoint is the last post-store. An empty prefix has equal
initial and final stores. A finished observation permits a finite silent
suffix ending at a return and keeps the last store at that suffix.

A closed singleton scheduler uses equality for every gap. An open component
admits exactly the pairs given by its environment relation. This interface
can express a peer's effect on the store, and the caller supplies the
relation. It carries neither peer control state nor a witness for individual
interleavings. For a whole program with multiple threads, Track A's scheduler
takes one successful primitive per turn, choosing a thread afresh. Its
events record the acting thread, but its event history omits full stores.
The two-thread regression uses that scheduler directly. The general
correspondence for arbitrary thread counts and the adequacy of any
environment relation as a scheduler projection remain open.

Tree prefixes use Track A's `Coalgebra.Follows` along a single path, with
finite silent moves preceding visible exchanges. A prefix can stop before
completion. `Returns` additionally requires a return layer, and
`ForestReturns` requires a root witness. Tau and both choice kinds are
internal in this weak observation. Track A's raw steps still distinguish
tau from selections and retain the kind and index of a selection. An empty
forest has no root. A zero-way choice can deadlock. A stuck visible request
in the general Track A model has an empty reply type. The requests here have
inhabited replies, and a gap failure means that a proposed observation fails
the store law. Divergence (even after an empty prefix), infinite visible
paths, fairness, and general stuckness are outside the finite comparison.
Track A's complete observations retain their distinct endings. A regression
checks that the weak ITree divergence has both an empty prefix and the
separate divergence observation.
[Track A interaction contract](track-a-interaction.md)
[Track A SC contract](track-a-concurrency.md)

## Checked laws

| Law | Statement |
| --- | --- |
| `follows_iff_machine` | A finite prefix of the embedded weak ITree is equivalent to a `MachineFollows` replay with the same frames and final store. The final tree is the image of the residual SC code. |
| `returns_iff_machine` | A finished observation is equivalent to replay ending at `Program.done`. |
| `returnTrace_ne_nil`, `returnTrace_iff_machine` | The transition-pair projection gives nonempty finished generators and the same generator predicate on the tree and replay sides, at each contextual pair of stores. |
| `forest_returns_iff_machine` | A finished forest observation is equivalent to a replay of one indexed initial program. |
| `choice_returns_iff_machine` | For either kind of finite CTree root choice, a finished observation is equivalent to replay of one chosen program. Zero alternatives permit no finished observation. |
| `closed_iff_sc` | Every finite singleton `sc.MTr` prefix admits contiguous frames, and every such replay projects to an `sc.MTr` prefix with the same program and store endpoints. |
| `closed_returns_iff_sc` | The singleton machine reaches done exactly when a finished tree observation projects to its event history with the same store endpoints. |

The independent replay judgment checks the actual `sequential` transition
at each supplied pre-store, using Track A's `primitive`. Its constructors
mention neither tree steps nor the tree store law. The proof compares the
weak visible layer with the primitive at each head command. The closed law
uses Track A's `single_run_iff` and the intermediate stores from the
singleton path. A finite CTree choice selects one entire component before
any request, independently of the SC scheduler's repeated per-primitive
selections.

The interference fixture runs a reader, then a peer writing 1, then the
reader again, from a cell initially 0. It checks the event list, the stores
at the gap, and that both threads finish. Filtering by the reader yields
replies 0 and 1. The projected frames form a finished open observation with
the 0-to-1 peer gap. The same frames fail closed continuity.
[Lean regressions](../../Silmaril/Proofs/Semantics/Brookes/TreeSC/Regression.lean)

The Track A race and reads-from predicates use positions in the full SC event
history. Filtering changes those positions and can erase the supplying
write, as in the fixture. In particular the bridge gives no transport of
race or reads-from predicates to the local frames, even though the event
projection preserves access mode. Mutex blocking, owner state, and any
classification of projected indices require additional hypotheses and laws.

## Models and extension point

`Code.toTree` builds the existing Lean `Silmaril.Elgot.ITree.Tree`.
`Code.forest` uses Track A's `WeakITree.toDelayed`, and the comparison
uses its actual weak destructor. The embedded programs come from an
inductive SC syntax. Arbitrary looping trees and nested CTree choices are
outside the adequacy theorems. The weak tree has already erased finite
tau structure. The original Coq ITree has explicit
`Ret`, `Tau`, and `Vis` layers, with `Vis` continuations indexed by the
response. The use of that shape here gives no theorem about the original
Coq library or its equivalences.
[ITree paper](https://doi.org/10.1145/3371119)
[Coq ITree definitions](https://github.com/DeepSpec/InteractionTrees/blob/master/theories/Core/ITreeDefinition.v)

The CTree definition here is Track A's finite-choice coalgebra and forest.
The original Choice Trees paper gives delayed and stepping branches distinct
induced transition rules and studies its own bisimulations. The C3 finished
law hides both root choices under the local weak policy. It says nothing
about their equivalence under the original induced LTS. The first-order
`Guarded.Forest.erase` already yields a Track A forest on dependent-sum
states, retaining the world in each request and updating its index on reply.
A guarded SC adapter can use that erasure followed by an explicit
world-preserving observation map with a store law. C3 checks the
world-independent read/write interface.
[CTree paper](https://doi.org/10.1145/3571254)
[Coq definitions from the POPL branch](https://github.com/vellvm/ctrees/blob/popl23/theories/Core/CTreeDefinitions.v)
[Lean guarded erasure](../../Silmaril/Semantics/TrackA/Interaction/Guarded/Thms.lean)

## C1 adapter seam

The planned C1 import is `Silmaril.Semantics.Brookes.Thms` in namespace
`Silmaril.Semantics.Brookes`. Its `Transition Store` is a store pair and
`Trace Store` is a raw list of pairs, including the empty list for contexts.
`Behavior Store Result` observes a nonempty trace and a terminal value.
It closes those observations under insertion of `(s, s)` anywhere and
contraction of adjacent `(s, t), (t, u)`, preserving the terminal value.
C1 admits gaps inside a trace and across sequencing.
[Brookes, LICS 1993, §5](https://doi.org/10.1109/LICS.1993.287596)
[Dvir–Kammar–Lahav–Plotkin, §6.1](https://arxiv.org/abs/2501.15104)

`Frame.transition` keeps exactly `(before, after)`. An arbitrary finite
prefix can project with `List.map Frame.transition` and may yield an empty
list. Only a `Returns` witness supplies a terminal value. For such a witness,
`returnTrace` projects each primitive if frames are present. With zero
frames the endpoints coincide and the generator is `[(s, s)]` at that
store. Taking these identity seeds over all stores fits the planned
`Behavior.ret`. A single primitive and its terminal value fit the seed
shape for `Behavior.atomic`. The two-thread regression projects to
`[(zero, zero), (one, one)]`, keeping the internal gap. A leading open gap
is reflected in the difference between the contextual start and the first
pair's pre-store. The generator carries the pairs and terminal value, with
the contextual stores available as external parameters. It inserts no
transition for a peer step.

The eventual adapter can close the equal generator predicates from
`returnTrace_iff_machine` with C1's actual closure. For inclusion, use
monotonicity of that closure. This transfers equality or inclusion of
closed behaviors; the extra stutters need no SC primitive witness. The C3
seed conditions still apply before closure, including contiguous stores for
the closed singleton case. C3 imports no C1 definitions.

For `Behavior.bind`, start from concatenation of two finished generator
lists using the first terminal value to select the second component. A
join intended to model C1 sequencing must allow the right pre-store to
differ from the left post-store. A comparison for a restricted C3 gap
profile needs a separate composition law with that profile at the join.
Ordered shuffle and closure for the Unit-result command view require a
separate scheduler projection theorem. The singleton-pair
initial/final-store observation can be compared after the carrier
comparison. A first naturality result can use a typed read/write signature
map that preserves replies, reads, and updates.

## Pinned integration and checks

The temporary review base `brookes/c3-track-a-integration` is
`ffeab6c3c1468e839beadee5eb2b04dd86d7355c`. It uses main at
`ad0442846393239063dcaea4b261e851287546b0` and the following two originally
unmerged sibling changes, applied with `git cherry-pick -x`.

| Dependency | Exact source commit |
| --- | --- |
| [Track A interaction #3543](https://github.com/hiloopai/silmaril-lean/pull/3543) | `61d4a44f4514730e0779c4180a768abc21086ed7` |
| [Track A SC #3539](https://github.com/hiloopai/silmaril-lean/pull/3539) | `0558a414b2117057e9b4ea638a8ceb1a3015827e` |

The C3 PR is based on this temporary branch so its review diff consists of
the bridge. Once both real dependencies land, rebase just the C3 commits
onto current main, recheck the bridge against the landed APIs, then push with
lease and retarget the draft to main.

```sh
git fetch origin main
git switch brookes/c3-tree-sc
git rebase --onto origin/main ffeab6c3c1468e839beadee5eb2b04dd86d7355c
lake build --wfail +Silmaril.Proofs.Semantics.Brookes.TreeSC.Regression
make check CHECK_TARGETS=+Silmaril.Proofs.Semantics.Brookes.TreeSC.Regression
git push --force-with-lease origin brookes/c3-tree-sc
gh pr edit brookes/c3-tree-sc --base main
```

On the pinned integration base, the strict build and scoped `make check`
above passed. The repository's kernel replay driver replayed all five
bridge modules against their built imports. The transitive axiom audit
covers the public theorem header and all regression theorems. Its only axioms are `propext`, `Classical.choice`,
and `Quot.sound`.
