# Coverage of the numbered CALCO 2019 examples

Paul Blain Levy and Sergey Goncharov,
[*Coinductive Resumption Monads: Guarded Iterative and Guarded Elgot*][paper],
CALCO 2019, article 13, pp. 13:1–13:17. The published PDF has SHA-256
`e9617e110c12a9ab2e99de57c75b2a23ed9191f6721afe92c0bba6a8b7ecb3ab`.
The numbered examples are 10 (p. 13:8), 20 (pp. 13:10–11), and 22
(pp. 13:11–12).

| Paper | Lean modules | Checked claims and scope |
| --- | --- | --- |
| 10(1), 20(1) | [SetModels][sets] | `Trunc` is inhabited exactly when the underlying type is inhabited. The concrete arrow is guarded in each summand and fails the guard for their union. The CALCO least guard gives unique fixpoints via `trunc_iterative`. |
| 10(2), 20(2) | [SetModels][sets], [Nonempty][nonempty] | `powersetElgot` instantiates the total CALCO Elgot interface and `powerset_least` proves leastness. `NonemptyPowerset.guard_holds_iff` identifies the direct-return guard, `laws_run` identifies the solution with `nonemptyIter`, and `guardedElgot` supplies the fixpoint, Conway, and pure uniformity laws. Membership is the library's predicate for a finite successful run. |
| 10(3), 20(3) | [Probability coverage][prob] | The published transition probabilities give eventual return mass `2/3`. The proposed normalization fails the fixpoint equation. There is a general unnormalized least solution for PMF bodies and an obstruction to natural, uniform PMF-valued iteration with the printed guard. |
| 10(4), 20(4) | [Printing][printing] | The all-recursive one-letter writer is guarded and has no finite-word fixpoint. [SingletonWriter][writer] checks the carrier, pure, and bind for the singleton extension and provides complete Elgot iteration via `elgot_isElgot`. The stream extension and the general left-action scope are tracked on the writer coverage page. |
| 10(5), 20(5) | [Printing][printing] | The finite-plus-infinite trace model checks the guard and the one-letter separating equation. Its finite-only and productive sets are nonempty, distinct fixpoints, ordered by inclusion. The no-output self-loop is unguarded. [Trace coverage][traces] identifies all three clauses by `greatest_iff`, gives the full law bundle in `productiveElgot`, and checks `canonical_not_least` and `productive_not_iterative`. |
| 22 | [Exceptions][exceptions] | For a total Elgot base on types, `resultSum` identifies the exception carrier with the paper's sum, `fibre` gives each CALCO Elgot monad. `ExceptT.adapt` preserves pure, bind, and iteration and defines the maps of the `parametrized` guarded Elgot functor. The abstract parametrized construction with an arbitrary guard and endofunctor is outside this example slice. |

The accounts of printing, I/O, and free extensions in the paper's introduction
are unnumbered. The table covers the three numbered examples.
See the [introduction coverage](calco2019-introduction.md) for the §1 models.

## Verification record

For the singleton-writer slice, the [draft CI workflow][writer-draft] concluded
`cancelled`. Its Lean job was skipped and its aggregate `CI` job was cancelled.
The [ready-for-review workflow][writer-ci] succeeded, including
`lean / check on prove`, `CI`, and `CI time budget / budget`.
The merged commit was `5cb10b7b030ecfcfb02163b5fd32384412b02b74`.
Its [main CI workflow][writer-main] also succeeded, including
`lean / check on prove`, `CI`, and `CI time budget / budget`.
A scoped `make check` on that commit passed with the five example views as
`CHECK_TARGETS`.

## Checking

```sh
lake build --wfail \
  +Silmaril.Papers.Calco2019.Examples.SetModels \
  +Silmaril.Papers.Calco2019.Examples.Printing \
  +Silmaril.Papers.Calco2019.Examples.Exceptions \
  +Silmaril.Papers.Calco2019.Examples.Probability \
  +Silmaril.Papers.Calco2019.Examples.SingletonWriter
```

[paper]: https://doi.org/10.4230/LIPIcs.CALCO.2019.13
[sets]: ../../Silmaril/Semantics/Calco2019/Examples/SetModels/Thms.lean
[printing]: ../../Silmaril/Semantics/Calco2019/Examples/Printing/Thms.lean
[exceptions]: ../../Silmaril/Semantics/Calco2019/Examples/Exceptions/Thms.lean
[prob]: calco2019-examples-probability.md
[nonempty]: ../../Silmaril/Semantics/Calco2019/Examples/SetModels/Nonempty/Thms.lean
[writer]: calco2019-examples-writer.md
[writer-draft]: https://github.com/hiloopai/silmaril-lean/actions/runs/45562378453
[writer-ci]: https://github.com/hiloopai/silmaril-lean/actions/runs/45562460187
[traces]: calco2019-examples-traces.md
[writer-main]: https://github.com/hiloopai/silmaril-lean/actions/runs/45564827540
