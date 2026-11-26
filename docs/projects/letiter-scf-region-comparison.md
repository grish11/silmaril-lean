# LetIter and the SCF loop boundary

This comparison treats a single [MLIR SCF while boundary](https://mlir.llvm.org/docs/Dialects/SCFDialect/#scfwhile-scfwhileop)
whose regions are native positional LetIter terms. The before state and the
condition payload have separate interfaces. A false condition passes its payload
to the parent continuation. A true condition passes its payload to the after
region, whose yield supplies the next before state. The after region and parent
can capture ambient variables. Their argument does not give them access to the
before state's local slot.

## Existing observations

- The exact typed equational institution is
  `Silmaril.Isotope.Institution.LetIter.inst`. Its signature category is
  `InstrSig τ ε` with instruction maps. Sentences are equations of data-valued
  exact typing derivations in a fixed free context. Models are constructor
  algebras, reduct is along `LetIter.sigHom`, and satisfaction is equality of
  structural denotations (`LetIter.sat_iff`).
- The native observational institution, `Observational.letIter Φ`, uses
  `Discrete ℕ` at fixed instruction alphabet `Φ`. Its models provide an
  environment and primitive return, fault and divergence relations. Its
  full-answer relation `Tm.Obs` records returned values with final machine
  states, faults with final machine states, and divergence from an initial
  state. Stuck terms contribute none of those observations. The native
  `iter_obs_iff` relates `Tm.Obs` to validity of observational equations.
- `continuationObs_iff_answerObs` proves that equality of full answers
  coincides with equality after **every** native call-by-value continuation on
  positional LetIter. Sequencing is a congruence and returning the newly
  bound value is the identity test. `Examples.erasing_continuation` exhibits
  the loss from fixing the continuation to unit: the two sum tags become
  indistinguishable under that test and remain distinct as full answers.

## Comparison

`RegionLoop.lower` uses one native `iter`, encoding the condition as a sum and
the parent continuation as `let₁`. The region semantics instead follows
`RegionLoop.Backedge` from a true condition and yield, and `RegionLoop.Exit` at
a false condition. It tracks finite backedge prefixes for returns and faults,
and a coinductive backedge relation for divergence. Individual region bodies
use the native LetIter semantics on both sides.
`RegionLoop.observe_eq_iterBeh` proves preservation and reflection at every
native observational model, including nondeterministic and stateful models.
`RegionLoop.WellTyped.lower` preserves exact typing. The checked closed example
starts with a tagged state, yields once through a unit payload, and runs a
parent that constructs a pair. The modified yield gives an infinite execution.

`lowerDiscrete` is a comorphism into the existing discrete-scope observational
institution. `regionInstitution` and `nativeInstitution` also use a common
signature category `Scope`. Its objects are finite context lengths and its
arrows are all maps of positions. At each scope:

- **Sen** consists of observational equations and refinements. Reindexing
  renames both sides. `RegionLoop.rename_id`, `RegionLoop.rename_comp`,
  `Tm.rename_id` and `Tm.rename_comp` give the identity and composition laws.
- **Mod** is the discrete category on the native observational models.
  `reductFunctor` precomposes the environment by the renaming.
  `reduct_id`, `reduct_comp`, `reductFunctor_id` and `reductFunctor_comp`
  state the reduct and functor laws.
- **Sat** is equality or inclusion of the program behaviour sets.
  `iterBeh_rename` and `RegionLoop.observe_rename` give the change-of-notation
  laws used to build the room functors.

`lowerComorphism` uses identity signature and model maps. Its sentence
translation commutes with renaming by `RegionLoop.lower_rename`; the
comorphism preserves and reflects satisfaction for equations and refinements
at each model. The separate syntactic operation `RegionLoop.bsubst` permits
term substitution under region binders.
`RegionLoop.bsubst_id`, `RegionLoop.bsubst_comp` and
`RegionLoop.lower_bsubst` check its laws. For inert substitutions, `iterBeh_bsubst` and
`RegionLoop.observe_bsubst` also prove equality of full answers after
replacing the environment by the substituted values. Signature morphisms
in this institution use variable renaming.

## Typed scalar SCF and CF

`ScalarWhile.toRegionLoop` realizes the typed `While` from
[PR #3167](https://github.com/hiloopai/silmaril-lean/pull/3167).
It embeds each of its four individual blocks as a typed primitive call.
The names of those primitives carry the block code. For a fixed interface,
one model interprets the symbols from any loop with that interface using the
given scalar primitive interpretation and ambient input. Native LetIter
controls entry, the branch on the condition tag, the backedge and the parent
continuation. `ScalarWhile.toRegionLoop_wellTyped` checks the resulting
LetIter interface with distinct state and payload types.

`ScalarWhile.returns_iff` proves that every LetIter return has the typed
result profile and a corresponding finite scalar run, and every finite
scalar return appears in LetIter. `ScalarWhile.diverges_iff` matches the
native coinductive divergence to the scalar evaluator's absence of a result
at every finite budget. `ScalarWhile.no_fault` checks that the pure scalar
realization has no fault observation. `ScalarWhile.cf_returns_iff` and
`ScalarWhile.cf_diverges_iff` compose these agreements with the independent
SCF-to-CF lowering.

## Native LambdaSSA and partial iteration

`RegionLoop.compile` calls `Morphism.SSAIter.compileSingle` on the native
LetIter lowering. `RegionLoop.ssaBeh_compile` proves the resulting region
preserves and reflects all parent observations in every native model.
Finite answers carry exit label zero. Faults and divergence retain their
original observations. `lowerLambdaSSA` composes the two discrete-scope
institution comorphisms. `ScalarWhile.toLambdaSSA_hasType` checks the
compiled scalar result type at the single exit.

`ScalarWhile.denotePart` applies the repository's Elgot iteration in
`Part` to the typed scalar step, including evaluation of the parent on
exit. `denotePart_eq_iter_bind` uses Elgot naturality to factor that
interpretation into partial iteration to the payload followed by the
parent. `mem_denotePart_iff` identifies membership with a finite run of
the independent SCF fuel evaluator. `denotePart_eq_none_iff` identifies its
undefined result with divergence in this deterministic, total-primitive
fragment. The LambdaSSA bridge proves finite returns, divergence, and
absence of faults separately. The checked raw LetIter example has identical
finite returns for a stuck term and a diverging term, which the full
observations distinguish.

`total_repeat_not_natural` isolates the obstruction even at an inhabited
return type. The body `Unit → Bool ⊕ Unit` always takes its backedge.
Mapping Boolean negation over its return summand leaves the body unchanged,
so naturality for a total iterator would force its chosen Boolean to be a
fixed point of negation. `repeatBool_partial` checks that the same body
has undefined iteration in `Part`.

The sum tags in this comparison are operational constructors. Categorical
coproduct claims depend on the quotient. The joined projection-return and
unit-η quotient fails `CopairPure`; the opt-in `WithCaseReturns`
extension proves it and supplies finite coproducts on discard-preserving
values. The finite constructor coproducts on singleton computation
quotients are a separate result. [Value obstruction](https://github.com/hiloopai/silmaril-lean/pull/3156) · [Opt-in value coproducts](https://github.com/hiloopai/silmaril-lean/pull/3165) · [Computation coproducts](https://github.com/hiloopai/silmaril-lean/pull/3117)

## Scope of the claim

The full observations are at the parent boundary. They omit individual
condition decisions and counts of yields. The comorphisms compare the
region view to LetIter's observational institution. The scalar realization
relates the deterministic pure dialect at a fixed profile and input to that
view. Its code blocks are interpreted as whole primitive calls, so this
realization does not lower individual scalar instructions. Typed SCF
signature change across profiles and a reverse translation for general
LetIter remain open. A comparison to the exact equational institution
would require a corresponding class of operation algebras and a separate
satisfaction result.
