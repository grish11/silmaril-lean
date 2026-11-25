# Productive trace iteration in CALCO 2019

[Example 20(5)][paper], p. 13:11, lists three ways to observe a trace. A finite
sequence of calls can end in a return or in an explicit infinite trace.
An infinite sequence of calls contributes the concatenation of its words.
[Paths][paths] represents the first two cases with `FiniteTraceRun` and the
third with `InfiniteTracePath` and `chunkStream`.

`greatestTrace` is the greatest fixpoint of the set-valued unfolding.
`greatest_iff` identifies its observations with exactly the three clauses
for arbitrary guarded bodies. In the infinite case, the proof chooses a
single coherent infinite sequence. The nonempty-word guard ensures that
its concatenation has a letter at every finite position. `greatest_nonempty`
shows that any body of nonempty trace sets has a nonempty solution under
this guard.

[TraceMonad][monad] checks pure and bind on the finite-plus-infinite trace
carrier and its nonempty subtype. `traceStep_eq_bind` identifies the
set-valued unfolding with Kleisli composition.

[TraceIteration][iteration] provides `productiveGuard`, `productiveIter`,
`productiveLaws`, and `productiveElgot`. Naturality follows by prefixing
each finite result with its continuation and preserving infinite traces.
The reverse inclusion uses the nonempty-word guard to exclude finite
observations that could be unmatched after arbitrarily many recursive
steps. Codiagonal follows from greatestness and naturality. Pure uniformity
transports postfixed families along the state map in both directions.
Proposition 17 supplies dinaturality.

`canonical_not_least` compares the chosen solution with the finite-only
fixpoint. For an alphabet with a letter, `productive_not_iterative` gives
the concrete failure of unique guarded fixpoints.

```sh
lake build --wfail +Silmaril.Papers.Calco2019.Examples.Printing
```

[paper]: https://doi.org/10.4230/LIPIcs.CALCO.2019.13
[paths]: ../../Silmaril/Semantics/Calco2019/Examples/Printing/Paths/Thms.lean
[monad]: ../../Silmaril/Semantics/Calco2019/Examples/Printing/TraceMonad/Thms.lean
[iteration]: ../../Silmaril/Semantics/Calco2019/Examples/Printing/TraceIteration/Thms.lean
