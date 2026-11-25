# CALCO 2019 examples

This page tracks the numbered examples in Paul Blain Levy and Sergey Goncharov,
[*Coinductive Resumption Monads: Guarded Iterative and Guarded Elgot*][paper],
CALCO 2019, article 13, pp. 13:1–13:17. The published PDF has SHA-256
`e9617e110c12a9ab2e99de57c75b2a23ed9191f6721afe92c0bba6a8b7ecb3ab`.

## Examples 10(3) and 20(3)

[Probability.Defs][prob-defs] uses Mathlib's `PMF` for countably supported
probability distributions. `Guarded` requires a positive direct-return
probability at every state. `step` is the pointwise Kleisli fixpoint equation.
`approx` unfolds a loop a bounded number of times and discards unfinished runs.
`least` is the pointwise supremum of these finite approximants.
[Probability.Thms][prob-thms] proves that `least` is a fixpoint, lies below every
prefixed point, and has total mass at most one. A guard makes each row's mass
positive, so `normalized` constructs a PMF by dividing by that mass.

### The arithmetic on p. 13:10

The printed exit probability at state `n` is `1 / (2^n + 2)`. Write
`S(n) = 1/2 + 2^(-n)`. The exit and continuation probabilities in the paper
are `2^(-n-1) / S(n)` and `S(n+1) / S(n)`. The probability of first exiting
at state `n` from state zero is therefore `2^(-n-1) / S(0)`, or
`1 / (3 * 2^n)`. Summing the geometric series gives **2/3**. The printed
sequence weight `1/2^(n+2)` and total `1/2` differ from those calculated
using the printed transitions. Lean checks the exact printed hazard in `exit_printed`, the individual
path weight in `first_exit_probability`, the filtered geometric series in
`scaled_least`, and the total in `chain_mass_zero`. A constant exit label
recovers the paper's singleton-result loop.

### The normalization claim

To test the fixpoint equation, `coloredExit` labels the exit at zero `false`
and every later exit `true`. It preserves every printed step probability.
The unnormalized probability of `false` from zero is `1/3` and the total
return probability is `2/3`. Normalization assigns `false` probability
`1/2`, but a single unfolding with the same continuation assigns `1/3`.
`normalized_not_fixpoint` proves the inequality for this guarded PMF loop.
The paper-facing `example20_3_counterexample` checks the guard and states the
failure directly in the categorical Kleisli fixpoint equation.

A probability-valued fixpoint can be produced by supplying an explicit fallback
distribution. `completion` assigns the missing mass to the fallback and
proves both unit mass and the original fixpoint equation. When termination has
probability one at each state, the underlying least solution already has unit
mass. Under that hypothesis `normalized_pmf_fixpoint_of_mass_one` proves the
categorical fixpoint equation for the normalized PMF.

There is also an obstruction to replacing normalization with a different
operator on the same guard. `no_nat_iteration` proves that even state and
result type `ℕ` admit no family of PMF-valued solutions satisfying the fixpoint
equation, naturality for pure result maps, and uniformity for pure state maps.
Label each exit by its state. Uniformity restricts a solution to any tail of
the chain. Naturality under translation of the result labels rules out mass
on earlier exits on that tail. The fixpoint equations then force the weight
of every individual label at state zero to equal the corresponding finite
exit probability. Those weights sum to `2/3`, while a PMF has mass one.

The [Kleisli theorems][kleisli] verify `pmfGuard` against the three axioms of
Definition 6. `no_conway_uniform` applies the pure-map obstruction to the
CALCO interface in Definition 19(2), using the inherited coproducts on types.

## The complete Elgot subdistribution monad

[Subdistribution][subdist] uses the paper's weight functions of mass at most
one. `Subdist.countable_support` derives the countable-support property.
`Subdist.solve` takes the pointwise supremum of the finite unfoldings on any
subdistribution body. `solve_weight`, `fix`, and `least_solution` identify
the operator and its least-fixpoint property. Its `Elgot.LawfulElgotMonad`
instance proves fixpoint, naturality, codiagonal, and pure uniformity.
`Subdist.elgot` and `Subdist.isElgot` provide the full CALCO bundle,
including dinaturality. `Subdist.pmf_agreement` checks that the total operator
on embedded PMF bodies agrees with the unnormalized weights above.

For full distributions, `no_total_fixpoints` also checks the paper's
empty-result-type argument independently of the positive direct-return guard.

## Checking

```sh
lake build --wfail +Silmaril.Papers.Calco2019.Examples.Probability
```

[paper]: https://doi.org/10.4230/LIPIcs.CALCO.2019.13
[prob-defs]: ../../Silmaril/Semantics/Calco2019/Examples/Probability/Defs.lean
[kleisli]: ../../Silmaril/Semantics/Calco2019/Examples/Probability/Kleisli/Thms.lean
[prob-thms]: ../../Silmaril/Semantics/Calco2019/Examples/Probability/Thms.lean
[subdist]: ../../Silmaril/Semantics/Calco2019/Examples/Probability/Subdistribution/Thms.lean
