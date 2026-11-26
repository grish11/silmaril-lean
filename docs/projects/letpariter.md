# LetParIter

Import `Silmaril.SSA.Isotope.LetParIter.Thms` for the iteration tier of the
shared `Silmaril.Isotope.Parallel.Tm`. In the `LetParIter` scope, `p || q`
takes two computations in the same free and bound contexts. If they return
`A` and `B`, the result is `product A B` in branch order. The branches
cannot refer to each other's bound results. They may use the same variables
and their instructions may interact through shared state. Destructure the
result with `let₂` when subsequent code needs both values. The ordinary
`pair` still evaluates its arguments from left to right.

`iter` uses the native LetIter typing convention. The seed supplies a value
of type `A`. Its body has one additional bound slot of type `A` and returns
`coprod B A`. The left injection returns a `B` and the right injection
supplies another `A`. A parallel computation can appear in the seed or in
the body, and either branch of a parallel computation can itself iterate.

[Syntax and embedding](../../Silmaril/SSA/Isotope/LetParIter/Defs.lean) ·
[Typed examples](../../tests/ssa/LetParIter.lean)

## Equations

`LetParIter.Equiv` is the inductively generated equivalence at fixed free
context, bound context and result type. Its endpoints retain exact typing
derivations. This keeps the intermediate types consistent through a rule,
including when multiple choices of intermediate types type-check the same raw
term. The inductive constructors give reflexivity, symmetry, transitivity,
congruence for every compound term constructor, type-preserving bound renaming,
and simultaneous bound substitution with pure images. Under a binder the
substitution preserves the new variable and weakens its older images. Iteration
congruence compares seeds in the ambient context and bodies in the extended
context. It introduces no equation relating iteration to parallel pairing.

The parallel generators are tuple swap and reassociation, projection past
either pure unit, agreement with the sequential product of two certified pure
terms, and naturality for pure result maps. The inherited case rules also
allow a branch to choose a case arm before the fork when the scrutinee is
certified pure. In each arm the unchanged partner is weakened into scope.
Syntactic purity is the shared `Parallel.Pure` predicate at the primitive
effect bottom for soundness. Both operands of a pure parallel term have to be
pure. An iteration has no purity constructor.

The mixed syntax also has pure let beta, let eta, feedback unfolding and the
native feedback seed-binding equation. The `native` constructor admits the
existing `LetIter.ProofRelevant.LocallyNameless.TypedEquiv` judgments at exact
native endpoints, including the native guarded uniformity premise and the
other sequential, case and Elgot equations there. The rule uses a proof at
the original typing derivations. The full native axiom schemata are not
automatically extended to mixed terms by this import. Full interchange for
two effectful continuations, effectful case distribution, and commuting
parallel with feedback have no generating equations.

[Equational constructors](../../Silmaril/SSA/Isotope/LetParIter/Equations/Defs.lean)

## Interpreting programs

Supply a lawful monad, its `Iterate` and `LawfulElgotMonad` instances, the
native type and instruction model, and an explicit
`Silmaril.Elgot.ParallelPairing m`. The record requires an ordered pairing,
naturality for ordinary functions via functor map, symmetry, associativity,
and the right unitor at monadic `pure ()`. The left unitor and compatibility
of pairing with one or two pure values follow from those fields. The record
has no law about Kleisli bind, iteration, scheduler fairness, or an effect
observation model. Use `LetParIter.interpret` to run the common tier evaluator
with this model. `interpret_eq_denote` relates that evaluator to the direct
native-model denotation. `interpret_sound` preserves the common evaluator
under every generated equation and every ambient valuation.

The model regression uses a partial writer whose bind adds counters and
whose parallel operation takes their maximum. The two sequential orders for
identical increments produce two, while the parallel operation produces one.
A separate example refutes full bind interchange. This writer is a check on
the generic assumptions. An operational shared-state interpretation supplies
its own pairing and proves the record's fields for its chosen observations.

[Pairing record](../../Silmaril/Semantics/Elgot/Parallel/Defs.lean) ·
[Soundness](../../Silmaril/SSA/Isotope/LetParIter/Thms.lean) ·
[Model regression](../../tests/ssa/LetParPairingModel.lean)

## Native compatibility

`embed` is constructor-preserving and `toLetIter?` is its left inverse.
`derivation` preserves native exact typing. The embedding commutes with type-preserving
renaming, simultaneous bound substitution and the native inclusion from
LetCase. `denote_embed` preserves
native denotation in every model supplied with a pairing. The native
denotation on these terms is therefore independent of the chosen pairing
on that same model. This gives syntactic injectivity and conservativity of
the interpretation on native programs. Reflection of the extended
equational theory into native syntactic equality would require a separate
argument.

Run `make check CHECK_TARGETS="LetParTests LetParIterTests"` for the focused checks.
