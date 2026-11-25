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
`RegionLoop.lower_bsubst` check its laws. Signature morphisms in this
institution use variable renaming, so the model reduct needs only bound
values.

## Scope of the claim

The full observations are at the parent boundary. They do not report
individual condition decisions or count yields. This is a comparison to
LetIter's observational institution. A comparison to the exact equational
institution would require a corresponding class of operation algebras and a
separate satisfaction result. The SCF-facing side still uses native
LetIter regions. Relating it to the independent SCF while dialect requires
a common admissible primitive interpretation and a proof that its region
evaluations and parent outcomes realize this boundary semantics.
