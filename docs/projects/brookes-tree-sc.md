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

The next adapter can map each `Frame` to its `(before, after)` transition
pair and transport the finished witness using the closed carrier's own
return convention. The empty list of pairs erases the shared endpoint
store, so the adapter should retain that store or use the carrier's
designated identity trace. Attach a return witness exactly for
`Returns`. An empty `Follows` observation is a prefix and gives no return
witness by itself. Preserve the boundary stores and the
admitted gap profile during that map. Raw equality transfers through the same map and
closure on each side. Raw inclusions can be lifted once the actual
stutter/mumble closure supplies monotonicity. Stuttering inserts idle pairs,
and mumbling contracts adjacent pairs with matching intermediate stores. A
proof for bind can start with finished left prefixes, reusing the final
store as the right input and applying the same gap rule at the join.
Scheduler composition needs a separate peer-projection theorem. A first
naturality result can use a typed read/write signature map that preserves
replies, reads, and updates. Those steps depend on the closed/monadic carrier
and typed SC signature work. This slice exposes the raw input to both.
[Brookes, *Full Abstraction for a Shared-Variable Parallel Language*](https://doi.org/10.1006/inco.1996.0056)

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
bridge modules against their built imports. The transitive axiom audit covers the public theorem header and
all regression theorems. Its only axioms are `propext`, `Classical.choice`,
and `Quot.sound`.
