# Track A interaction institutions and iteration

This development extends the checked delayed interaction and UB definitions
from [Track A interaction and refinement](track-a-interaction.md). The
institution headers live in Logic, which can import both the institution API
and Semantics without a new region dependency.
[Institution header](../../Silmaril/Logic/TrackA/Interaction/Thms.lean)

## Signatures and satisfaction

`Signature.Hom S T` sends each request `q` to a target request and decodes its
response to a value of `S.Response q`. The composition laws are equalities of
the dependent records. `TraceSignature` keeps all signature objects and
restricts the arrows to maps whose backward response function at every request
is bijective. This supplies a forward response map and preserves emptiness of
the response type. Requests can still merge or leave some target requests
unmapped. A regression shows that removing the bijectivity requirement permits
a source request loop to acquire a stuck outcome after relabeling.
[Signature and relabeling definitions](../../Silmaril/Semantics/TrackA/Interaction/Relabel/Defs.lean)
[Regressions](../../Silmaril/Proofs/Logic/TrackA/Interaction/Regression.lean)

The four `ClassicInstitution` values use the opposite of `TraceSignature` as
their signature category. For an underlying map `f : S → T`, the model reduct
goes from `S` to `T`, in the direction of execution relabeling. The sentence
translation goes from `T` to `S` by inverse image. Model categories are
discrete. Satisfaction means inclusion in the sentence's allowed set.
[Institution definitions](../../Silmaril/Logic/TrackA/Interaction/Defs.lean)

The satisfaction condition follows Goguen and Burstall (1992), *Institutions: Abstract Model Theory for Specification and Programming*, §2.1,
Definition 1, printed pp. 101–102. The room functors use the category-of-models
variant of §2.5, Definition 12, printed pp. 109–110. The linked PDF has SHA-256
`f6715ca333dd03dc153a65907c1c974fa151690bb94eafffc065c363265b634d`.
[DOI](https://doi.org/10.1145/147508.147524) ·
[Definition 1, PDF pp. 7–8](https://courses.grainger.illinois.edu/cs522/sp2016/InstitutionsAbstractModelTheory.pdf#page=7) ·
[Definition 12 and category variant, PDF pp. 15–16](https://courses.grainger.illinois.edu/cs522/sp2016/InstitutionsAbstractModelTheory.pdf#page=15)

| Institution | Models | Model reduct along the underlying `f` |
| --- | --- | --- |
| `treeInstitution` | Rooted forests with fixed choice signature, result type and root index | Relabel each unfolding layer and keep the state carrier and roots |
| `traceInstitution` | Sets of complete weak traces | Direct image of traces |
| `explicitInstitution` | Sets of ordinary traces and an explicit UB marker | Direct image with the marker fixed |
| `catastrophicInstitution` | Saturated sets of ordinary traces and the marker | Direct image followed by saturation |

For forests the satisfaction condition uses `Forest.observes_relabel`. The
proof transports each finite run and reuses a single compatible state path
for each infinite run. For the first three institutions the set image and
preimage adjunction gives satisfaction. For the fourth, saturation adds a
second left adjoint. The closed bound pulls back to a closed bound since the
UB marker is fixed. The room functors check identity and composition for both
translations, including repeated saturation on model reducts.
[Relabeling theorems](../../Silmaril/Semantics/TrackA/Interaction/Relabel/Thms.lean)
[Institution proofs](../../Silmaril/Proofs/Logic/TrackA/Interaction/Institution.lean)

## Observation boundaries

Taking `Forest.observes` preserves and reflects each trace upper bound. It
records completed exchanges, returns, stuck requests, deadlock kind, silent
divergence and infinite exchange streams. It forgets the branching structure,
internal timing, choice indices and root provenance. Arbitrary trace sets
need not come with a realizing tree. The results concern this may-observation
semantics and do not identify it with bisimulation or a timed semantics.

For a forest returning `Option A`, `toExplicit` preserves ordinary complete
traces and sends every completed run returning `none` to one marker. The
marker witnesses such a run, and its exchange prefix is available only before
projection. `toCatastrophic` includes all the extracted behaviors. It preserves
them exactly on UB-free forests and permits all outcomes if any root returns
UB on any run. These are whole-row semantics. An explicit bound pulls back
along the classifier, and a closed catastrophic bound holds exactly when the
explicit observations lie in it. Both projections commute with the indicated
model reducts.
[UB projection and satisfaction theorems](../../Silmaril/Logic/TrackA/Interaction/Thms.lean)

## Iteration

`Elgot.guardedLoop` runs in the landed weak interaction-tree monad over the
indexed encoding of a dependent signature. Its body performs one request
before each exit or recursive call. `loop_observes_infinite` checks that
compatible replies generate a single infinite exchange path in the delayed
adapter. The source ITree has already erased finite silent timing.

`Elgot.interpret` specializes the existing iteration-preserving fold to a
handler returning a computation of each request's dependent response type.
The target has `LawfulMonad`, `Iterate` and `LawfulElgotMonad`. The latter
checks fixpoint, effectful naturality in returned values, codiagonal and
uniformity for pure state maps satisfying the Kleisli square. Source and
response values share a universe, and weak trees over that universe must
satisfy the fold's `Small` hypotheses. The interpreted guarded loop equals
target iteration of the handler followed by its typed continuation.
`interpret_guardedLoop_naturality` moves an effectful result continuation into
the exit arm, and `interpret_nestedGuardedLoop` merges two recursive exits
by codiagonal. These results apply to the weak ITree source and lawful Elgot
targets under those hypotheses. The delayed nondeterministic presentations
and the trace and UB institutions supply no target Elgot laws or general
handler-adequacy result.
[Guarded iteration header](../../Silmaril/Semantics/TrackA/Interaction/Elgot/Thms.lean)
[Elgot laws](../../Silmaril/Semantics/Elgot/Defs.lean)
[Iteration-preserving fold](../../Silmaril/Semantics/ITreeInterpret/Defs.lean)

## Checks

```sh
targets='+Silmaril.Logic.TrackA.Interaction.Thms +Silmaril.Semantics.TrackA.Interaction.Elgot.Thms +Silmaril.Proofs.Logic.TrackA.Interaction.Regression +Silmaril.Proofs.Semantics.TrackA.Interaction.Regression'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
for path in Silmaril/{Logic,Proofs/Logic}/TrackA/Interaction/*.lean \
  Silmaril/{Semantics,Proofs/Semantics}/TrackA/Interaction/{Elgot,Relabel}/*.lean \
  Silmaril/Proofs/Semantics/TrackA/Interaction/Regression.lean; do
  module=${path%.lean}
  LEAN_NUM_THREADS=1 SILMARIL_REPLAY_MODULE=${module//\//.} \
    lake env lean -DwarningAsError=true tools/compiler-explorer/Replay.lean || exit
done
```

The repository replay driver calls the pinned `LeanChecker.replayFromImports`
once per module. It replays each module's stored declarations over its loaded
imports using the Lean kernel.
