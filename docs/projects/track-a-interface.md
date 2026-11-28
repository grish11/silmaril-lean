# Track A sequential interfaces

Import `Silmaril.Semantics.TrackA.Interface.Thms`. The operators use the
[Track A interaction signature and coalgebra](track-a-interaction.md).

| Operation | Contract | Checked laws |
| --- | --- | --- |
| `Signature.restrict S P` | A request carries a proof of `P` and keeps its response type from `S`. | `inclusion_factor`, `inclusion_cancel`, and `factors_iff` give the unique factorization of a `Hom` whose request map lands in `P`. |
| `Signature.sum S T` | A request is tagged left or right. Its response is the corresponding fiber lifted into the common universe. | `copair_inl`, `copair_inr`, and `copair_eta` give existence and uniqueness of the coproduct map. |
| `Coalgebra.extend T c` | Lift `c` to the coproduct by tagging its requests left and decoding their lifted responses. | `extend_vis` gives the exact visible layer and `relabel_extend` computes dispatch through a copair. |
| `Renaming` | An equivalence of requests and a response equivalence at each request. `toHom` uses the inverse response equivalence to drive the old continuation. | `id_toHom`, `comp_toHom`, and the two inverse laws have the stated orientation of `Signature.Hom`. `relabel_rename_symm` recovers the original coalgebra. |
| `Coalgebra.hide P policy refusal c` | Keep selected requests visible. For each hidden request, consult the policy at the current state. A reply advances its typed continuation in one tau step. A refusal returns the supplied terminal result. | `hide_relabel_inclusion` recovers an included coalgebra. `hide_staged` combines stages with decreasing visibility and a shared refusal result, routing each hidden request to the first stage that hides it. |
| `Coalgebra.restrict P refusal c` | Apply hiding with a policy that refuses every unselected request. | `restrict_refuse` computes the refusal layer. |

`Signature.hom_ext` compares request maps pointwise and compares response
decoders after transporting a target reply along the resulting equality of
response types. `Renaming.symm` transports response types along the request
equivalence's inverse law. Coalgebra equalities here are equalities of
unfoldings on a common state carrier.

The hiding policy is a deterministic partial responder indexed by state and
request. Its only state advance is through the source continuation. When the
policy returns `none`, hiding terminates with the caller's `refusal` result.
The refusal has precisely the empty finite trace returning that result. A
supplied reply admits exactly the observations of the resulting successor in
the hidden coalgebra. A hidden request that loops after being answered can
diverge silently.

Use an explicit ordinary refusal such as `.error e` with result type
`Except Error Value`. At the Track A UB boundary, `UB.atBoundary` maps
`Set (Trace S (Option A))` to `UB.Explicit (Trace S A)`. With
`A = Except Error Value`, supply `some (.error e)` as the refusal result.
The boundary preserves it as an ordinary error trace. Supply the outer
`none` only for deliberate UB. A trace returning that value contributes
the UB marker and makes `UB.collapse` yield the catastrophic top.
[Track A UB definitions](../../Silmaril/Semantics/TrackA/Interaction/UB/Defs.lean)

The interpretation acts on the coalgebra before observation. It can select a
continuation via a typed response or end an execution via refusal. The
regression exercises both cases with a hidden Boolean read whose reply controls
the next public request. It checks that ordinary refusal survives boundary
collapse as a singleton without UB and that returning the outer `none`
collapses to top. It also checks an infinite sequence of visible reads that
becomes silent divergence under an internal response policy, and a renaming
that changes both the request and its reply encoding. The checked laws
concern sequential unfoldings and the Track A may-observation model.
SC path projection and preservation under concurrent composition are outside
this interface's scope.

## Checks

```sh
lake build --wfail +Silmaril.Semantics.TrackA.Interface.Thms +Silmaril.Proofs.Semantics.TrackA.Interface.Regression
make check CHECK_TARGETS='+Silmaril.Semantics.TrackA.Interface.Thms +Silmaril.Proofs.Semantics.TrackA.Interface.Regression'
lake env leanchecker Silmaril.Semantics.TrackA.Interface.Defs
lake env leanchecker Silmaril.Proofs.Semantics.TrackA.Interface.Laws
lake env leanchecker Silmaril.Semantics.TrackA.Interface.Thms
lake env leanchecker Silmaril.Proofs.Semantics.TrackA.Interface.Regression
```
