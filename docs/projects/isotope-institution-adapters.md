# Cross-tier Isotope institution adapters

All signature maps are in the shared `InstrSig τ ε` category. The comorphisms
use its identity functor. The exact sequential sentence API takes the types,
effects and free-name sorts in one universe. Relabeling preserves the declared source, target and
effect of each instruction. The sentence maps retain the two exact typing
derivations, including their bound types and binder witnesses.

## Lower tiers

`Silmaril.SSA.Isotope.Institution.Adapters.Powerset.Thms` gives
`Powerset.letSeq` and `Powerset.letCase`. Each includes the relational syntax
into the corresponding native parallel syntax and restricts that parallel
institution to the Mathlib `SetM` monad with a fixed operation for parallel
pairing. Each primitive interpretation is represented by its membership
relation. The strict model arrows have identity computation maps and preserve
the primitive sets. Taking membership sends each such arrow to a pointwise
relation inclusion. `Model.strict_arrow_iff` characterizes this restriction in
the native strict model category.

The equation maps commute with opcode relabeling, including the endpoint casts.
The model comparison commutes with signature reducts on objects and arrows.
The satisfaction equivalence uses exact native evaluation and extensional
equality of powersets. This use of powerset extensionality is local to the
restricted models.

The rooms fix the context, value family, product and unit interpretations,
and pairing operation. The case room also fixes coproduct and empty-type
equivalences. Lower primitive interpretations are arbitrary relations. Effect
annotations are preserved by relabeling, and the comparisons require no
semantic purity, pairing laws, or iteration.

Native lower observation compares the computations of the given endpoints.
The ordered writer fixture derives a relabeled swap whose observation fails
with ordered pairing, giving logs `[2, 7]` and `[7, 2]`. A semantics on a syntax
quotient needs a separate proof that its model laws validate the generating
equations on the relevant witnesses. [Ordered writer regression](https://github.com/hiloopai/silmaril-lean/blob/1aefb95777b0a1f261b6fdde490781ff708de141/tests/ssa/LetIterWeakTreeSoundness.lean#L420-L430)

The Brookes SC probe uses closed `Behavior (Store W) A` computations, concrete
SC opcode evaluations, and `Behavior.parallelPairing Store |>.pair`. In its
Boolean-owner signature, `acquire false` and `acquire true` have the same source,
target, and effect, so an `InstrSig` relabeling can exchange them. A fixed-primitive
Brookes profile additionally requires signature arrows to preserve the full SC
designation, including the owner, and reducts to preserve the designated
interpretation. The observation compares full closed behaviors. Singleton
projection can identify different full behaviors and discard gaps another
component can complete during scheduling. [Fixed-world Brookes model and singleton observation](brookes-sc-concrete.md#singleton-observations-and-interference)

## Upper tier

`Silmaril.SSA.Isotope.Institution.Adapters.Iteration.Thms` gives two
comorphisms into the native LetParIter institution.

- `Iteration.letParCase` widens exact LetParCase witnesses and uses the native
  LetParIter reduct. The reduct forgets iteration, retaining the lawful monad,
  instruction computations and the supplied pairing. Model arrows keep their
  strict computation maps, which preserve the retained operations. The
  comparison fixes the four value equivalences to those of the upper
  `TypeModel` and requires coverage of visible free valuations.
- `Iteration.letIter` includes exact LetIter witnesses from the monadic
  companion. The companion uses the native sequential evaluator and the same
  strict model category as LetParIter. Upper models supply a lawful monad,
  lawful Elgot iteration, a symmetric parallel pairing, and both primitive
  computations and coherent pure interpretations of bottom-effect instructions.
  The companion's satisfaction is equality of native computations. Its
  sentence and signature reduct laws use the same fixed witnesses and the
  upper institution's change-of-signature law.

Upper free environments store every context slot, including anonymous and
shadowed slots. Lower free environments assign values to visible bindings.
`Iteration.visibleEnv_surjective_iff` states that every visible valuation lifts
exactly when existence of a visible valuation implies existence of a full
upper environment. A full environment supplies values for hidden slots while
the visible valuation supplies the visible values. This condition holds for
the empty context. `Iteration.nativeBound_get` gives a lift of every bound
valuation.

The anonymous-empty-slot regression gives an exact case equation with a
visible valuation and unequal computations. The case reduct refutes the
equation, and native upper satisfaction is vacuous because the full context
has an empty slot.

For the fixed native powerset model, `Iteration.set_satisfaction` also compares
the image of a LetIter equation directly with its relational satisfaction.
It uses the repository's lawful finite-success `SetM` iteration, the same
primitive computations viewed by membership, and a supplied symmetric
powerset pairing. Bottom-effect instructions must have coherent pure
interpretations. The comparison applies on the same visible environment
coverage as the case reduct.

The `UpperPowerset` institution bundles that profile over all native
LetParIter sentences. Signature reducts retain the fixed monad, Elgot
iteration, and pairing, and transport primitive computations and coherent
pure interpretations using the source, target, and effect equalities. For
a fixed pairing, its model arrows are precisely upper strict arrows with
identity computation maps, preserving both primitive interpretations.
`UpperPowerset.letIter` and `UpperPowerset.letParCase` use this shared target.
The case comparison takes the underlying operation of the upper pairing as
the lower profile's `ParOp`. The reduct squares `Model.toCase_reduct` and
`Model.toRelational_reduct` commute on objects and arrows. Both paths take
membership of the same primitive computations.

`Silmaril.SSA.Isotope.Institution.Adapters.Thms` exposes the commuting
sentence squares and outer rectangle, using equality of exact witnesses.
It also states equality of the lower, upper, and outer corridors on
both sentence and model components. The upper square and outer rectangle
commute as bundled comorphisms on the same powerset profiles. The sequential
path of the outer rectangle uses `Relational.seqIterCoHom`.

In the upper square, `caseIter_model_commutes` gives equality of the two
backwards functors at each instruction signature. The parallel route
retains the primitive membership predicates in the lower powerset model,
then views them as relations. The sequential route takes those same
membership predicates directly, and the sequential case-to-iteration
inclusion has the identity model functor. Both routes send an upper strict
identity computation map to the inclusion of equal primitive predicates.
The existing reduct laws make these comparisons compatible with signature
maps. Free-environment coverage supplies the satisfaction equivalence.

The underlying syntax is proof relevant. These maps apply to each given
endpoint witness. A raw syntax descent requires separate compatibility of the
generating equations and endpoints. See the [tagged partial-model witness separation](https://github.com/hiloopai/silmaril-lean/commit/9936e209bd6244b2f27722216b2f129e59f7f541).

## Regression checks

The adapter examples and transitive axiom audit are leaf modules under
`Silmaril.Proofs.SSA.Isotope.Institution.Adapters.Regression`. The audit imports
the examples, so its path-selected target checks both.

```sh
lake build --wfail +Silmaril.Proofs.SSA.Isotope.Institution.Adapters.Regression.Axioms
```
