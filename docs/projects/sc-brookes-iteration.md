# Finite SC iteration and tuple-returning parallel

Import [`Silmaril.Semantics.Brookes.Iteration.Thms`][iteration] for the model
and its laws, or [`Silmaril.Semantics.Brookes.Parallel.Thms`][parallel] for
parallel without the order and iteration imports. The carrier and its
directional stuttering and mumbling are those of the [finite trace core][core]
from [PR #3594][core-pr].

## Equations for an interpreter

- `Behavior.ret y` closes singleton identity transitions labelled by `y`.
  `p.bind k` closes concatenation with the continuation selected by the
  first return. `p.mapResult f` changes the result label and equals
  `p.bind (ret ∘ f)`.
- `p.parallel q` closes all order-preserving shuffles of one word from
  each operand, with terminal result `(a, b)`. `parallel_generate`
  gives the same behavior when shuffling nonempty seeds before closing.
  `parallel_natural`, `parallel_symm`, `parallel_assoc` and the two
  `parallel_unit` laws use the ordinary product maps, swap, associator and
  projections. `parallel_pure` gives `ret (a, b)` for two pure operands.
  `forget_parallel` recovers the core unit-result command semantics.
- For a body `f : X → Behavior Store (Y ⊕ X)`, `inl y` returns and
  `inr x` recurs. At each `x`, `approx f 0 x = ⊥` and
  `approx f (n+1) x = (f x).bind (Sum.elim ret (approx f n))`.
  `iterate f x` is the union over `n`, ordered by inclusion of word and
  result observations. Bind preserves unions in either argument.
  Unfolding is ω-Scott continuous, and `iterate_eq_fix` identifies the
  union with Silmaril's Kleene fixed point. `iterate_least` gives
  leastness among all pre-fixed points.
- The `LawfulElgotMonad` instance checks fixpoint, naturality in the
  postcontinuation, codiagonal, and uniformity for pure changes of loop
  state. `iterate_strength` carries a fixed pure context `d` through
  every call and pairs it with the returned value. `iterate_parallel_ret`
  gives the same law using parallel with `ret d`.

These are semantic equations over the trace carrier. The LetParIter syntax,
its generic interface, and a theorem interpreting its derivable equations
need the separate interface development. In particular, interchange for
arbitrary effectful operands cannot be a sound equation for this model.

## Closed observations and interchange

`Behavior.completes s t r` observes the singleton word `[(s, t)]` with
result `r`. For parallel, this holds exactly when a finite shuffle of
accepted operand words has a contiguous run from `s` to `t`.
`Runs.of_reduces` ensures that closing a word cannot create a contiguous
run across an unmatched store boundary.

`interchange_inclusion` embeds every schedule of
`(p.parallel q).bind (fun (a, b) => (k a).parallel (l b))` into
`(p.bind k).parallel (q.bind l)`. The first expression requires both
first stages to finish before either continuation runs. The reverse
inclusion fails even on singleton observations. Start with store `0`.
The left thread writes `1` then reads. The right thread writes `2` then
returns unit. The independent schedule runs the left write and read
before the right write and accepts `[(0, 2)]` with result `(1, ())`.
In the staged expression the read occurs after both writes. Its parallel
partner is a pure return, so the read observes the final store `2`.
`shared_store_interchange_strict` checks both claims after closure.

## Termination scope and sources

Each observed loop result has a finite bound by `iterate_accepts_iff`.
The regressions exhibit a store-changing loop that completes after two
calls and a writing loop with no return path whose entire behavior is
bottom. A pure return at an initial store gives a singleton observation
that bottom lacks. Divergence and any other absence of a completed trace
are observationally identified. The model observes possible finite
completions. Fair infinite executions, divergent prefixes, and
must-termination are outside this observation model.

- Stephen Brookes, *Full Abstraction for a Shared-Variable Parallel
  Language*, Information and Computation 127(2), 145–163 (1996).
  Section 6 gives the finite transition traces and closed interleaving.
  Section 10 adds fair executions. [DOI][brookes] · [Author's scan][brookes-pdf]
- Yotam Dvir, Ohad Kammar, Ori Lahav and Gordon D. Plotkin, *Two-sorted
  algebraic decompositions of Brookes’s shared-state denotational
  semantics*, FoSSaCS 2025, 377–398. Section 6.1 gives the single-sorted
  return-bearing carrier and Kleisli extension. [DOI][two-sorted-doi] ·
  [arXiv v3][two-sorted]
- Sergey Goncharov, Lutz Schröder, Christoph Rauch and Julian Jakob,
  *Unguarded Recursion on Coinductive Resumptions*, LMCS 14(3), 2018.
  Section 5 gives complete Elgot iteration and the construction from
  ω-continuous monads. [DOI][elgot] · [Publisher PDF][elgot-pdf]

The core crosswalk records hashes for the first two sources. The LMCS PDF
cited here has SHA-256
`cae43f18e77550eafe726b475a9998098c047b45ebb00763df6c2d6284b8fc81`.

## Checks

```sh
make check CHECK_TARGETS='+Silmaril.Semantics.Brookes.Parallel.Thms +Silmaril.Semantics.Brookes.Iteration.Thms +Silmaril.Proofs.Semantics.Brookes.Regression +Silmaril.Proofs.Semantics.Brookes.IterationRegression'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/semantics/brookes/IterationAxioms.lean
```

[core]: sc-brookes.md
[core-pr]: https://github.com/hiloopai/silmaril-lean/pull/3594
[parallel]: ../../Silmaril/Semantics/Brookes/Parallel/Thms.lean
[iteration]: ../../Silmaril/Semantics/Brookes/Iteration/Thms.lean
[brookes]: https://doi.org/10.1006/inco.1996.0056
[brookes-pdf]: https://www.cs.cmu.edu/~brookes/papers/FullAbstractionSharedVariable.pdf
[two-sorted-doi]: https://doi.org/10.1007/978-3-031-90897-2_18
[two-sorted]: https://arxiv.org/pdf/2501.15104v3
[elgot]: https://doi.org/10.23638/LMCS-14(3:10)2018
[elgot-pdf]: https://lmcs.episciences.org/4784/pdf
