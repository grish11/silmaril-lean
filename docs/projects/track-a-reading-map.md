# Track A reading map

Track A gives a typed vocabulary for interactions, observation and refinement,
a finite primitive concurrency model, and two admitted SQLite storage cases.
The table identifies the observation point for each result and links to
the statements and checks.

## Reading order and evidence

| Question | Statements and checks |
| --- | --- |
| What does an interaction expose? | A request determines its response type. An exchange pairs a request with a completed response. `Coalgebra.observes_tau`, `observes_visible_loop`, `observes_handle_vis`, and `obsEq_iff_mutual_refines` cover silent steps, an infinite exchange path, stateful handling and refinement. The countdown regression has completed runs of every finite length and no infinite exchange path. [Interaction guide][interaction] · [Header][interaction-thms] · [Regression][interaction-check] |
| What does the guarded fragment add? | `Guarded.Forest.step_vis` checks erasure of a first-order, context-indexed visible step whose reply determines the next context. `WeakITree.observes_diverge` checks the delayed adapter's representation of weak-tree divergence by a silent self-loop. [Guarded header][guarded-thms] · [Weak-tree header][weak-thms] |
| What survives relabeling and signature change? | `Forest.observes_relabel` transports observations by direct image for signature maps with bijective response decoders. Requests may merge. The four institutions use the opposite signature category, and satisfaction checks inclusion in an allowed observation set. `tree_trace_satisfaction`, `tree_explicit_satisfaction` and `tree_catastrophic_satisfaction` relate forest satisfaction to the three trace bounds. The regression shows why dropping response bijectivity can introduce stuckness. [Institution guide][institution] · [Relabeling header][relabel-thms] · [Institution header][institution-thms] · [Regression][institution-check] |
| Where does Elgot iteration apply? | `loop_observes_infinite` witnesses a single path from compatible replies in the request-guarded loop. `interpret_guardedLoop`, `interpret_guardedLoop_naturality` and `interpret_nestedGuardedLoop` use the existing weak ITree fold into a lawful Elgot target under the stated `Small` hypotheses. [Iteration header][elgot-thms] |
| How is undefined behavior (UB) represented? | A finite tree observation ending in `returned none` retains its exchanges. `UB.atBoundary_ub_iff` witnesses such a run after projection to a single marker that drops its prefix. `collapse_eq_top_iff` and `val_collapse_of_safe` describe whole-row saturation and exactness on UB-free rows. [UB header][ub-thms] · [Boundary and relabeling][relabel-thms] |
| What are the C1 nonempty, bottom and trace transformer laws? | `addBottom_le_iff` and `addBottom_surjective` recover the catastrophic order by adjoining bottom. `Nonempty.no_common_lower_bound` rules out a common lower bound for distinct singleton outcomes in the nonempty fragment. With `[Subsingleton T]` and `t : T`, `Nonempty.pure_le_all` makes `pure t` least. `Arrow.then_assoc` and `Arrow.then_mono` give associative and monotone composition. `bind_eq_top_iff` locates UB in the first row or a reachable continuation row. [UB header][ub-thms] |
| What is sequentially consistent (SC)? | `replay_iff` relates each finite primitive execution to its schedule. `classifyHistory_eq_some_iff` ties validation to generated executions, and a regression rejects a forged read that the raw classifier calls clean. `guarded_iff_filtered` equates ordinary guarded runs with clean raw runs. `racy_run_has_ub_prefix` and `raceUB_has_raw_run` connect raw executions to the first racing extension. The examples check a lock cycle with a separate completing schedule and a race-free run of SC atomic loads and stores that loses an update. [SC and race guide][sc] · [Header][sc-thms] · [Examples][sc-check] |
| When can a concurrent trace be projected? | `Interface.observedRun_inter` factors filtered observations while retaining a source execution witness. `Projection.happensBefore_eq` requires retained cross-thread edge endpoints and, for the mixed profile, coverage of intervening overwrites. `Projection.classify_eq` additionally requires conflict coverage. `atomicSync_eq` compares the raw Boolean. A reads-from interpretation requires a generated SC history and increasing positions. The examples hide a handoff, overwrite or conflict, and check that repeated labels map to distinct source occurrences. [Projection guide][sc-projection] · [Header][projection-thms] · [Examples][projection-check] |
| How are sequential interfaces combined? | `factors_iff` and `copair_eta` cover request restriction and tagged sum. `relabel_extend` checks extension and dispatch. With a typed renaming both requests and reply fibers have equivalences. `observes_hide_reply`, `observes_hide_refuse`, `observes_hide_loop` and `hide_staged` cover a state-indexed partial reply policy, including refusal and silent divergence. [Operator guide][operators] · [Header][operators-thms] · [Regression][operators-check] |
| Which SQLite source is being read? | The inventory pins SQLite 3.54.1, including the amalgamation digest and split source at `57520227c95396ce39ba6ecaac8d475b78dd3964`. The operation notes follow rowid lookup and rollback-journal insert/commit through VDBE, B-Tree, Pager and VFS, with instrumented source fixtures. [Version and interfaces][inventory] · [Operation paths][operations] |
| What does the admitted read prove? | `staged_eq_composed` compares full staged and composed outcomes. `composed_trace` validates the recorded exchanges with the supplied handler. `readOnly_cold_warm_lookup` proves the same lookup and poststates after one complete cold page read and a warm acquisition with zero exchanges. The check module covers found and absent keys, cold/warm traces and a truncated file. [Read case][read-case] · [Header][read-thms] · [Checks][read-check] |
| What does the open typed read expose? | `vfsTree_corresponds` witnesses the open VFS tree's complete trace along the supplied handler's replies. `vfsTree_readOnly_cold_warm` gives the typed cold/warm observations. `handledPager_returns_staged` hides the Pager request and returns the complete staged outcome, including file/cache poststates and exchanges. [Typed read guide][typed-read] · [Header][typed-read-thms] · [Checks][typed-read-check] |
| How do the handled read paths agree? | `Read.Adapter.interpretations_agree` gives the same one-call result, file and cache poststates, and completed exchange history for the handled Pager path, the handled VFS path from #3572, and `Read.runStaged`. The exchanges validate the backing transition. The open-tree statement is membership of the complete trace selected by the backing handler’s actual replies. [Adapter guide][read-adapter] · [Header][read-adapter-thms] |
| What does a repeated read check? | The Pager handler threads the file, cache and history across acquisitions and reuses #3572’s `pagerHandler`. `pagerTwice_agrees` passes the first call’s actual file and cache to a second call with the same page and key, preserves the starting history, and validates the appended exchanges in order. Given matching image bytes, an existing page view, a live handle, an admitted range and leaf, and a vacant owned slot, `pagerTwice_readOnly_cold_warm` gives equal lookups and exactly one full-page cold exchange in the initially empty history. The fixture also checks an existing history entry and counts the backing calls for present and absent keys. [Adapter guide][read-adapter] · [Header][read-adapter-thms] · [Checks][read-adapter-check] |
| What does the selected rollback-mode write prove? | For `insertAndCommit` after operand admission and fresh-key leaf preflight, `run_follows_schedule` validates the completed calls, first error and handler poststate. `database_write_requires_journal` orders any database write attempt after a successful preimage write and journal sync. Under the packed-page and backing assumptions, `commit_success` reopens to the inserted row and all old rows, and `journal_sync_failure` retains the preimage and leaves the database unchanged on the selected fault. `run_observes` embeds the handler-selected trace and `no_ub` excludes the tree's explicit UB marker. [Write case][write-case] · [Header][write-thms] |

## Where the terms apply

- **May observation and refinement.** The observations record possible
  completed exchanges and terminal outcomes, silent divergence, and
  infinite exchange streams. Refinement is inclusion from implementation to
  specification. Both raw choice kinds are hidden and count as internal
  progress. Branching structure, choice indices, finite internal timing and
  root provenance are erased by observation. Bisimulation, must behavior
  and timing equivalence are outside these statements. [Interaction guide][interaction]
- **Guarded, handled and hidden.** Context-indexed requests and replies
  apply to the first-order guarded fragment. The Elgot fold has its own
  weak-tree source and lawful target assumptions. Higher-order effects,
  general handler adequacy and Elgot laws for the delayed choice model are
  outside this scope. Sequential hiding answers a request before
  observation or returns a designated refusal. SC projection filters an
  already generated history. [Guarded header][guarded-thms] · [Iteration header][elgot-thms] · [Operator guide][operators] · [Projection guide][sc-projection]
- **UB and ordinary errors.** A racing SC prefix is the raw trace through
  the attempted racing extension. The interaction UB marker denotes a
  completed run returning `none` at a chosen boundary, and saturation
  admits every trace in that row when the marker is present. The correspondences here supply no translation
  from SC race prefixes to catastrophic rows. A modeled VFS error or
  rejected short read is an ordinary return. At `UB.atBoundary`, a hiding
  refusal such as `some (.error e)` stays ordinary. Handling the Pager and exposing
  the lower VFS use different observation points. [SC header][sc-thms] · [UB header][ub-thms] · [Typed read guide][typed-read] · [Write case][write-case]
- **SC, races and calls.** SC orders primitive actions. The race
  definitions operate on event positions, with mutex synchronization and,
  in the mixed profile, atomic reads-from edges on generated histories.
  The raw label tests can accept impossible histories before validation.
  The model has no scheduler fairness or starvation guarantee. Race freedom supplies no
  general atomicity or linearizability of compound calls, as the lost-update
  example illustrates. [SC and race guide][sc] · [Examples][sc-check]
- **SQLite admission.** The read starts at acquisition of a designated
  512-byte packed rowid leaf with an open handle. The Lean model rejects
  short reads, while the pinned C main-file path can pass the buffer with
  its unread suffix zero-filled to page-format admission. The write starts after transaction setup
  with an admitted cursor, resident leaf and open journal in the canonical
  two-page model. In pinned C, journal opening precedes the dirty mark,
  and preimage recording precedes marking the page writable. The model
  starts with the journal open and represents the later cached leaf edit.
  Its selected sync acknowledgements express ordering. Callers composing
  individual public Pager stages supply the prerequisites themselves.
  Whole SQL execution, C or native refinement, WAL, contention, durability
  and crash recovery are outside these claims. [Operation paths][operations] · [Read case][read-case] · [Write case][write-case]

## Implementation on main

Implementation pin `f4e150fb9424a0c030c6a662d18d078adbbbdd82` contains all ten
merges below. On the read path, #3555 supplies the concrete read,
#3572 adds `Read.Interaction`, and #3623 adds the stateful `Read.Adapter`.

| Slice | Merge on main |
| --- | --- |
| [SQLite source inventory #3531][pr-inventory] | `36dac76adaee65c557c00ab2d9df372851495898` |
| [Primitive SC and races #3539][pr-sc] | `59e2500ddc9e3b59f393e134259081c80392ab71` |
| [Interaction and refinement #3543][pr-interaction] | `9c5d64ca9f1d4fbb36f213bd634d608b58dc6642` |
| [Concrete SQLite read #3555][pr-read] | `ea34d1ac0d0e4c7471c049769a10f38b6dacb932` |
| [Open typed read #3572][pr-typed-read] | `f20bc085ccf72ba77bfd882823a11deb60556a38` |
| [Stateful read adapter #3623][pr-read-adapter] | `26a59ab4f3131bde9cee45053d678fa5b961886f` |
| [SC projection #3559][pr-projection] | `905623e5ac5c74564e86daba44920e58ff63cd69` |
| [Sequential interface operators #3564][pr-operators] | `abff074efabd68b7df45ed9fe87f6c7a37b9ed21` |
| [Institutions and guarded Elgot interpretation #3576][pr-institution] | `ce7eb116bab0b7f4365b4aec1174a483abf4518a` |
| [Rollback-mode SQLite write #3580][pr-write] | `f4e150fb9424a0c030c6a662d18d078adbbbdd82` |

## Validate the implementation pin

The commands select 52 Lean modules from the first-parent deltas of
these ten merges. The build treats warnings as errors and `make check`
runs the repository source gates with that target list. Kernel replay
checks each selected module over its loaded imports.

```bash
set -euo pipefail
implementation=f4e150fb9424a0c030c6a662d18d078adbbbdd82
merges=(
  36dac76adaee65c557c00ab2d9df372851495898
  59e2500ddc9e3b59f393e134259081c80392ab71
  9c5d64ca9f1d4fbb36f213bd634d608b58dc6642
  ea34d1ac0d0e4c7471c049769a10f38b6dacb932
  f20bc085ccf72ba77bfd882823a11deb60556a38
  26a59ab4f3131bde9cee45053d678fa5b961886f
  905623e5ac5c74564e86daba44920e58ff63cd69
  abff074efabd68b7df45ed9fe87f6c7a37b9ed21
  ce7eb116bab0b7f4365b4aec1174a483abf4518a
  f4e150fb9424a0c030c6a662d18d078adbbbdd82
)
git fetch --no-tags origin "$implementation"
git worktree add --detach ../track-a-main-check "$implementation"
cd ../track-a-main-check
test "$(git rev-parse HEAD^{tree})" = dc875a869d582c207f387cf50e85d4e89d698086

paths=$(mktemp)
trap 'rm -f "$paths"' EXIT
for merge in "${merges[@]}"; do
  git merge-base --is-ancestor "$merge" "$implementation"
  git diff --name-only --diff-filter=ACMR "$merge^1" "$merge" -- '*.lean'
done > "$paths"
mapfile -t modules < <(LC_ALL=C sort -u "$paths" | sed -e 's/\.lean$//' -e 's@/@.@g')
test "${#modules[@]}" -eq 52
targets=("${modules[@]/#/+}")
export LEAN_NUM_THREADS=12
lake build --wfail "${targets[@]}"
make check "CHECK_TARGETS=${targets[*]}"
printf '%s\n' "${modules[@]}" | xargs -r -P 6 -n 1 bash -c '
  LEAN_NUM_THREADS=1 SILMARIL_REPLAY_MODULE="$1" \
    lake env lean -DwarningAsError=true tools/compiler-explorer/Replay.lean
' _
```

## Historical checks

The detached integration recipes predate the merges on main. The earlier
#3583 snapshot includes `lowered_observations_eq`. The #3623 candidate
snapshot records the stateful adapter and its scoped checks before the
implementation merges. [Historical #3583 recipe][historical-integration] · [Historical #3623 recipe][historical-stateful-integration]

[interaction]: track-a-interaction.md
[interaction-thms]: ../../Silmaril/Semantics/TrackA/Interaction/Thms.lean
[interaction-check]: ../../Silmaril/Proofs/Semantics/TrackA/Interaction/Regression.lean
[guarded-thms]: ../../Silmaril/Semantics/TrackA/Interaction/Guarded/Thms.lean
[weak-thms]: ../../Silmaril/Semantics/TrackA/Interaction/WeakITree/Thms.lean
[ub-thms]: ../../Silmaril/Semantics/TrackA/Interaction/UB/Thms.lean
[institution]: track-a-interaction-institution.md
[institution-thms]: ../../Silmaril/Logic/TrackA/Interaction/Thms.lean
[institution-check]: ../../Silmaril/Proofs/Logic/TrackA/Interaction/Regression.lean
[relabel-thms]: ../../Silmaril/Semantics/TrackA/Interaction/Relabel/Thms.lean
[elgot-thms]: ../../Silmaril/Semantics/TrackA/Interaction/Elgot/Thms.lean
[sc]: track-a-concurrency.md
[sc-thms]: ../../Silmaril/Semantics/TrackA/Concurrency/Thms.lean
[sc-check]: ../../Silmaril/Proofs/Semantics/TrackA/Concurrency/Examples.lean
[sc-projection]: track-a-concurrency.md#interface-observations
[projection-thms]: ../../Silmaril/Semantics/TrackA/Concurrency/Projection/Thms.lean
[projection-check]: ../../Silmaril/Proofs/Semantics/TrackA/Concurrency/Projection/Examples.lean
[operators]: track-a-interface.md
[operators-thms]: ../../Silmaril/Semantics/TrackA/Interface/Thms.lean
[operators-check]: ../../Silmaril/Proofs/Semantics/TrackA/Interface/Regression.lean
[inventory]: sqlite-track-a/header-inventory/README.md
[operations]: sqlite-track-a/header-inventory/operations.md
[read-case]: sqlite-track-a/read-case.md
[read-thms]: ../../Silmaril/Machine/SQLite/TrackA/Read/Thms.lean
[read-check]: ../../Silmaril/Machine/SQLite/TrackA/Read/Checks.lean
[typed-read]: sqlite-track-a/read-interaction.md
[typed-read-thms]: ../../Silmaril/Machine/SQLite/TrackA/Read/Interaction/Thms.lean
[typed-read-check]: ../../Silmaril/Machine/SQLite/TrackA/Read/Interaction/Checks.lean
[read-adapter]: sqlite-track-a/typed-read-adapter.md
[read-adapter-thms]: ../../Silmaril/Machine/SQLite/TrackA/Read/Adapter/Thms.lean
[read-adapter-check]: ../../Silmaril/Machine/SQLite/TrackA/Read/Adapter/Checks.lean
[write-case]: sqlite-track-a-write.md
[write-thms]: ../../Silmaril/Machine/SqliteVfs/TrackA/Write/Thms.lean
[pr-inventory]: https://github.com/hiloopai/silmaril-lean/pull/3531
[pr-sc]: https://github.com/hiloopai/silmaril-lean/pull/3539
[pr-interaction]: https://github.com/hiloopai/silmaril-lean/pull/3543
[pr-projection]: https://github.com/hiloopai/silmaril-lean/pull/3559
[pr-operators]: https://github.com/hiloopai/silmaril-lean/pull/3564
[pr-read]: https://github.com/hiloopai/silmaril-lean/pull/3555
[pr-typed-read]: https://github.com/hiloopai/silmaril-lean/pull/3572
[pr-institution]: https://github.com/hiloopai/silmaril-lean/pull/3576
[pr-read-adapter]: https://github.com/hiloopai/silmaril-lean/pull/3623
[pr-write]: https://github.com/hiloopai/silmaril-lean/pull/3580
[historical-integration]: https://github.com/hiloopai/silmaril-lean/blob/f3b9c32dbb606bca3afd0fc97eb80bc584768411/docs/projects/track-a-reading-map.md#reproduce-the-checked-integration
[historical-stateful-integration]: https://github.com/hiloopai/silmaril-lean/blob/61349da9ca21e4e405e0f70386c3d72590bdcebf/docs/projects/track-a-reading-map.md#reproduce-the-checked-integration
