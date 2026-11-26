# Generalized institution evaluation

Import `Silmaril.Logic.Institution.Generalized.Thms` for the interface and laws.
The starting point is the satisfaction condition in Goguen and Burstall,
*Institutions: Abstract Model Theory for Specification and Programming* (1992),
§2.1, Definition 1, and the distinction from semantic consequence in §2.2,
Definition 2(9). The existing `goguen-burstall-1992` entry records the DOI and
artifact hash. [Bibliography](../../references.bib)

## Evaluation and consequence

`ExactInstitution Sign D` uses the sentence functor `Sen : Sign ⥤ Type` and
model functor `Mod : Signᵒᵖ ⥤ Cat` of `ClassicInstitution`. For `σ : S ⟶ T`,
a model `M` over `T` and a sentence `φ` over `S`, `eval_map` gives

```text
eval T M (Sen.map σ φ) = eval S (reduct σ M) φ.
```

The two evaluations are elements of the same fixed type `D`. A lattice is one
choice of `D`. The exact law works with any value type. In a
`TypedInstitution Sign Denote`, the type code `t` and its denotation
`Denote t` are fixed across signatures. Each `Sen t` is a functor, so
translation of syntax at that type preserves identities and composition.
`atType t` gives an exact institution with value type `Denote t`.

`observe P` reads a value as satisfaction by applying a fixed predicate
`P : D → Prop`. It keeps the sentence functor and the entire model functor,
and its `ClassicInstitution` can be used as a room functor via `toRoomFunctor`.
The induced consequence `Evaluation.entails P Γ φ` says every model that passes
`P` on each premise in `Γ` also passes `P` on `φ`. The theorem
`ExactInstitution.entails_iff_room_entails` identifies this with the existing
`Room.Entails`. The existing corridor laws then give preservation under
translation and reflection when the reduct is surjective on models.
[Classic API](../../Silmaril/Logic/Institution/Basic.lean) ·
[Room laws](../../Silmaril/Logic/Institution/Room.lean)

`ExactInstitution.ofClassic` and `toClassic` are inverse at `D = Prop`.
`toTyped` embeds a fixed value type as a singleton family and `atType`
recovers it. For a typed family, `propInstitution` uses an equivalence
`Denote t ≃ Prop` to read the designated propositional fiber. This also
accommodates a lifted `Prop` in a higher universe.
A predicate observation can identify different values. The checked example
with the predicate `0 ≤ ·` gives values 1 and 0 the same satisfaction result.
Recovering a general value from one observation would require additional data.
[Definitions](../../Silmaril/Logic/Institution/Generalized/Defs.lean) ·
[Examples](../../Silmaril/Logic/Institution/Generalized/Examples.lean)

## Order-lax evaluation and upper cuts

`LaxInstitution` requires a preorder. Its orientation is
`eval S (reduct σ M) φ ≤ eval T M (Sen.map σ φ)`. For composable signature
maps both functors compute the composite and `le_eval_map_comp` chains the
inequalities. The upper cut at `k` passes from reduct to target by
`cut_preserved`. It is an ordinary institution with the given functors and
cut exactly when `ReflectsCut k` holds. In a partial order, all upper cuts
reflect iff the evaluation law is equality. The example where evaluation is
the signature number has an exact cut at zero. At threshold one, the map
from zero to one gives a passing target and a failing reduct.
[Cut laws](../../Silmaril/Logic/Institution/Generalized/Thms.lean)

## Three and four values

A three-valued evaluator can return `some true`, `some false`, or `none`.
`Evidence.ofThree` embeds these into two independent proposition flags, with
`none` setting neither. Four-valued evaluators can also set both flags.
`Evidence` orders values by implication in each flag, the information order.
A producer chooses the meaning of each flag.

`Evidence.ofCompletions C P` uses universal satisfaction and universal
refutation, expressed as `∀ x ∈ C, P x` and `∀ x ∈ C, ¬ P x`. A mixed family has neither
flag, and an empty family has both by vacuity. When `C` is inhabited, the two
flags cannot both hold. Taking a subset can only add flags in the information
order. A reduct preserving `P` yields the same flags as its image of `C`.
A covering reduct therefore gives equality with the full source family.
`Evaluation.entailmentEvidence` takes `C` to be the models of the observed
premises. Its positive flag is ordinary entailment after observation. The
negative flag requires every such model to refute the observed conclusion.
A single countermodel suffices to disprove ordinary entailment, even when
other models still satisfy the conclusion. The completion flags encode a
different question from whether witnesses for either answer exist.
[Completion laws](../../Silmaril/Logic/Institution/Generalized/Thms.lean)

Build the interface, proofs and examples with

```sh
lake build --wfail +Silmaril.Logic.Institution.Generalized.Examples
```
