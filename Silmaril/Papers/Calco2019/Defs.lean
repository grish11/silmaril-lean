module

public import Silmaril.Semantics.Calco2019.Defs
public import Silmaril.Semantics.Calco2019.Nested
public import Silmaril.Semantics.Calco2019.Parametrized
public import Silmaril.Semantics.Calco2019.ResumptionGuard
public import Silmaril.Semantics.Calco2019.GuardedTransformations

/-!
# Coinductive Resumption Monads: Guarded Iterative and Guarded Elgot

Paul Blain Levy and Sergey Goncharov, CALCO 2019, Article 13.
DOI: [10.4230/LIPIcs.CALCO.2019.13](https://doi.org/10.4230/LIPIcs.CALCO.2019.13).
Publisher PDF SHA-256: `e9617e110c12a9ab2e99de57c75b2a23ed9191f6721afe92c0bba6a8b7ecb3ab`.

Numbered definitions in `Silmaril.Calco2019`:

* Definition 1: `Bimodule`.
* Definitions 2–3: `Bimodule.FreeExtension`, `Bimodule.FreeObject`.
* Definition 6 and Notation 7: `Guardedness`, `MonadGuardedness`, `Guardedness.nestedMany`.
* Definition 11: `MonadGuardedness.Preserves`, `MonadGuardedness.GuardedNatTrans`.
* Definition 12: `Guardedness.Iterative`.
* Definition 14: `Guardedness.Conway`.
* Definition 16: `Guardedness.Fixpoints.Uniform`.
* Definition 19: `IsGuardedIterative`, `GuardedElgotMonad`, `GuardedElgotMonad.IsElgot`.
* Definition 21: `ParametrizedGuardedElgotMonad`.
* Guarded natural transformations in Theorem 28: `GuardedTransformation`, `guardedBimodule`.
* Definition 24: `ParametrizedGuardedElgotMonad.ResumptionGuard`.
-/
