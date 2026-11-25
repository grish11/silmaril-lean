# Concrete models in the CALCO 2019 introduction

[Levy and Goncharov, CALCO 2019, article 13][paper], §§1.1–1.3, pp. 13:2–5.
See the [numbered examples][examples] for Examples 10, 20, and 22.

| Source | Concrete model and coverage |
| --- | --- |
| §1.1, pp. 13:2–3 | The finite-word and productive printing monads are covered under Examples 10(4–5) and 20(4–5). The two complete Elgot printing models in the introduction additionally retain the finite output of a hanging computation. |
| §1.2, pp. 13:3–4 | The paper specifies initial and final coalgebras for deterministic printing, and uses the countable nonempty powerset for printing and general signature I/O. The unrestricted nonempty trace powerset in Example 20(5) does not impose the countable branching condition of these resumption instances. |
| §1.3, p. 13:5 | [Delay][delay] checks the identity-base, identity-operation case with Mathlib's raw `Computation` type, which keeps every explicit delay. |

## Capretta delay

`Delay.coalgebra` observes a return or a single further delay.
`terminal` proves finality by the strong bisimulation principle for
`Computation`. `resumptions` supplies the chosen final coalgebras of the
actual CALCO parameter family. `obj_eq` and `out_eq` identify the carrier
and destructor. `unit_eq` and `extend_eq` identify the resumption monad's
return and Kleisli extension with `Computation.pure` and `Computation.bind`.
`free` specializes the CALCO free guarded Elgot object theorem.

The citation to Capretta [5] identifies the underlying coinductive
datatype for intensional partiality. The Lean instance checks the raw
delay monad on types. The interpretation of general recursion in an
intensional type theory is Capretta's external result.

```sh
lake build --wfail +Silmaril.Papers.Calco2019.Examples.Delay
```

[paper]: https://doi.org/10.4230/LIPIcs.CALCO.2019.13
[examples]: calco2019-examples.md
[delay]: ../../Silmaril/Semantics/Calco2019/Examples/Delay/Thms.lean
