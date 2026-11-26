# The native LetParIter institution

Import `Silmaril.SSA.Isotope.LetParIter.Institution.Thms` for the core.
`Silmaril.SSA.Isotope.LetParIter.Institution.Restrictions.Thms` adds the
exact fragment restrictions and the native soundness corollary.
The let-family entry point `Silmaril.SSA.Isotope.Institution.Thms`
also exposes both headers. The definitions are in
`Silmaril.Isotope.LetParIter.Institution`.
[Native syntax and evaluator](letpariter.md)

## Signatures and equations

`inst ν` is a functor from the native `InstrSig τ ε` category to
`Silmaril.Logic.Institution.Room`. It fixes the type system, bottom
effect, and native value interpretation. A signature map relabels
primitive instructions, preserving their source, target, and effect
exactly. Preservation of the effect also preserves and reflects
bottom purity.

Each sentence consists of two terms at one free context, bound
context, and result type. Each endpoint contains its own exact
`Parallel.Derivation`, including the types chosen at intermediate
binders. `Sentence.map` relabels both endpoints and transports their
instruction indices along the signature map. It preserves the
identity and composition laws on the whole sentence.
[Definitions](../../Silmaril/SSA/Isotope/LetParIter/Institution/Defs.lean)

## Models and satisfaction

A model supplies a monad `Carrier : Type v → Type v` at the universe
of the value interpretation, a chosen lawful Elgot iteration,
symmetric `ParallelPairing`, and a native `InstructionModel`. The
fixed `TypeModel` gives all models the same carriers for values,
structural equivalences, and environments. A strict arrow acts
on computations at every value type and preserves pure, bind,
iteration, parallel pairing, and Kleisli instruction denotation.
It also preserves the ordinary functions for bottom-pure
instructions, which is an explicit law even when monadic pure
can identify values.

`Model.eval` applies the native `LetParIter.denote` to the exact
endpoint derivation. `Sat` requires equality of the resulting
computations at every free and bound environment. A model reduct
precomposes the two instruction interpretations with the
signature map and retains the underlying model operations.
`Model.eval_reduct` compares the translated endpoint's evaluation
with the original endpoint's evaluation in the reduct.
Applying it to both endpoints gives the satisfaction condition.
[Core theorems](../../Silmaril/SSA/Isotope/LetParIter/Institution/Thms.lean)

## Exact fragment comparisons

`Model.evalShared_eq_eval` compares the common tier interpreter
and native evaluator at the same derivation and environments.
It uses the same instructions, chosen iteration, and pairing.
The parent agreement theorem uses a lawful monad and chosen
iteration. `satisfaction_iff_evalShared` applies this result to
the two stored witnesses individually.

For a native LetIter derivation `d`, `Expr.ofLetIter d` stores
`LetParIter.derivation d`. The sequential restriction retains
iteration and evaluates `nativeTyping d` in the same value and
instruction models. `satisfaction_ofLetIter` establishes truth
agreement for a pair of these exact endpoints. The native
`Equiv` generator takes `TypedEquiv.Related` at the corresponding
`nativeTyping` endpoints. The separate `satisfaction_of_equiv`
corollary uses native soundness and the Elgot laws.

`Expr.ofLetParCase` supplies the exact case-tier widening.
`Model.evalLetParCase` retains pairing, instructions, and the
case control, using the free and bound lookup projections.
A comparison with the lower institution requires the widening
evaluation square and any environment coverage and naturality
laws for that institution. Comparison of chosen derivations
and descent to quotients are separate questions.
[Restriction definitions](../../Silmaril/SSA/Isotope/LetParIter/Institution/Restrictions/Defs.lean) ·
[Restriction theorems](../../Silmaril/SSA/Isotope/LetParIter/Institution/Restrictions/Thms.lean)

## Regression

The independent `Part` fixture runs a feedback loop beside a
partial probe. A false seed takes a recursive step before exiting.
A nonidentity signature map adds an instruction label. The
translated sentence and its source reduct hold with the returning
probe and fail with the undefined probe. The fixture also checks
the shared evaluator on the stored translated endpoint.
The fixture lives in the existing `Silmaril` library scope, so
CI selects it through its source path and imports.
[Checked fixture](../../Silmaril/Proofs/SSA/Isotope/LetParIter/Institution/Regression.lean)

```sh
lake build --wfail +Silmaril.Proofs.SSA.Isotope.LetParIter.Institution.Regression
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.Isotope.LetParIter.Institution.Regression'
```
