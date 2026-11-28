# Concrete SC signatures on Brookes traces

Import [`Silmaril.Logic.BrookesSC.Concrete.Thms`][concrete] for the
fixed-world institution. It instantiates the [SC signature API][signature]
with the [finite Brookes carrier][core]. It has no dependency on an interaction
tree bridge.

## Store and interpretation

`Concrete.Store W` has dependent memory `(c : W.Cell) → W.Value c` and
ownership `W.Mutex → Option W.Thread`. The executable `Store.step` generalizes
the signature example's deterministic step, using decidable equality on cells,
mutexes and threads. Loads return the current typed value. Stores update just
the specified cell. Both memory modes have the same SC effect. Acquire succeeds
only on a free mutex and assigns its owner. This includes blocking reentrant
acquire. Release succeeds only for its owner and clears ownership. Stores and
successful mutex operations return `PUnit`.

`primitive_accepts_iff` gives the exact singleton generators and their
stuttering and mumbling closure. With no legal generators, the behavior is
empty. A legal step may have stutters inserted at any boundary, even before
acquire at a held store if there is a gap to a free store. On the singleton
observation, `primitive_completes_iff` recovers the exact step, including the
guard, reply and updated store.

`Concrete.target W` orders behaviors by inclusion of whole transition words
with their terminal replies. A `TraceModel` chooses a closed behavior for each
external label in its reply sort. `eval_ret` uses Brookes return, whose seeds
are identity transitions at arbitrary stores. `eval_call_primitive_ret`
normalizes a primitive followed by immediate return of its reply. A call
selects its continuation by reply and closes concatenation. In
`eval_call_primitive_accepts_iff` the store after the primitive and the store
before the continuation are independent. `eval_call_external` uses the
model's chosen external behavior in the same bind.

`Concrete.institution W` is a functor from `Signature W` to rooms.
`satisfies_iff` expresses trace inclusion at every input. For a model arrow
`M ⟶ N`, `eval_mono` gives inclusion of `M.eval program` in `N.eval program`
for the same program.
`eval_translate`, `reduct_external` and `satisfaction` give the translation
and reduct equations. A signature arrow forwards labels in each full
designation fiber of the same world. The full designation fixes the primitive
and its mode or the external reply sort. General event maps, hiding, and
changes of world need additional data and laws.

## Singleton observations and interference

Import [`Concrete.Observation.Thms`][observation] for `observe`, which keeps
the initial store, final store and reply of singleton words. `observe_bind_iff`
proves relational composition with a matching middle store for this
observation, including reply-dependent continuation. `observe_eval` gives the
same results through the relational `stateTarget`. `observeModelFunctor`
preserves refinement and commutes with signature reducts by
`observeModelFunctor_reduct`. Trace satisfaction implies singleton satisfaction
by `observe_satisfaction`.

A state-only composition with matched stores cannot reconstruct open words with
an environment transition at the join. The checked write/read-back inequation
holds on singleton observations and fails on full traces when the environment
writes between the two accesses. Similarly, projecting components to singleton
relations before scheduling can discard the gapped behavior that another
component would complete via a shuffle. The [Brookes core regression][parallel]
exhibits such a schedule. The finite behaviors concern successful completed
traces. Race classification, liveness and operational adequacy for a source
language require separate proofs.

## C3 adapter API

- Supply one `World` and decidable equality on `W.Cell`, `W.Mutex` and
  `W.Thread`. Track A's [shared-store memory][track-a] has type
  `Resource → Nat`. Its homogeneous instance here uses
  `Cell := Resource` and `Value := fun _ => Nat`. For a dependent world,
  preserve the cell index through payloads, replies and both stores of each
  transition.
- For primitive and external events, use `Signature.Op` indexed by the full
  `Designation`. Supply `TraceModel.external` as a
  `Behavior (Store W) (W.ExternalReply sort)` for each external label.
  `primitive_accepts_iff` and `primitive_completes_iff` give the two forms of
  the primitive boundary. `eval_ret`, `eval_call_primitive` and
  `eval_call_external` are the program equations.
- Use `Concrete.institution W` for full-word judgments and `satisfaction`
  for fixed-world designation-preserving renamings. Use `observe_eval` when
  the adapter's observation is explicitly a contiguous run on one store.
  Track A's scheduled events and race labels would need their own
  correspondence. Both SC modes have identical store effects here.

## Reproduce the checks

The [regression][regression] checks a nonidentity label map and its reduct on
a reply-dependent sentence that changes truth between two models. It also
checks the write/read-back distinction, mutex guards and the difference between
stuttering before a legal step and closing an empty generator.

```sh
lake build --wfail +Silmaril.Proofs.Logic.BrookesSC.Concrete.Regression
make check CHECK_TARGETS='+Silmaril.Proofs.Logic.BrookesSC.Concrete.Regression'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/logic/brookes-sc/ConcreteAxioms.lean
```

For kernel replay, set `SILMARIL_REPLAY_MODULE` to each of the following
modules in turn and run
`lake env lean -DwarningAsError=true tools/compiler-explorer/Replay.lean`.

- `Silmaril.Logic.BrookesSC.Concrete.Defs`
- `Silmaril.Proofs.Logic.BrookesSC.Concrete.Interpretation`
- `Silmaril.Logic.BrookesSC.Concrete.Thms`
- `Silmaril.Logic.BrookesSC.Concrete.Observation.Defs`
- `Silmaril.Proofs.Logic.BrookesSC.Concrete.Observation`
- `Silmaril.Logic.BrookesSC.Concrete.Observation.Thms`
- `Silmaril.Proofs.Logic.BrookesSC.Concrete.Regression`

[concrete]: ../../Silmaril/Logic/BrookesSC/Concrete/Thms.lean
[signature]: brookes-sc-institution.md
[core]: sc-brookes.md
[observation]: ../../Silmaril/Logic/BrookesSC/Concrete/Observation/Thms.lean
[parallel]: ../../Silmaril/Proofs/Semantics/Brookes/Regression.lean
[regression]: ../../Silmaril/Proofs/Logic/BrookesSC/Concrete/Regression.lean
[track-a]: https://github.com/hiloopai/silmaril-lean/blob/b93f7a72e2ad4a244ffd17bb5e94858a2c73fc3b/Silmaril/Semantics/TrackA/Concurrency/Defs.lean
