# Finite SC Brookes traces

Import [`Silmaril.Semantics.Brookes.Thms`][thms]. The core uses Lean's
prelude and an arbitrary store type, with no database, language, or memory
layout dependency. On the starting main commit `69c66716febfb727a1649779a62ee71d78f2d838`,
`Semantics.Operational.Execution` provides operational executions,
`Semantics.ITree` provides interaction trees, and `Semantics.TraceModels`
contains trace-valued examples. The inventory found no Brookes carrier or
stuttering/mumbling algebra. The open Track A interaction, primitive SC,
and projection work are future comparison points. [#3543][interaction] ·
[#3539][primitive] · [#3559][projection]

## Primary sources and correspondence

- Stephen Brookes, *Full Abstraction for a Shared-Variable Parallel Language*,
  Information and Computation 127(2), 145–163 (1996). Section 6 and
  Propositions 6.1–6.2 give the terminating transition traces, the two
  deductions, `skip`, concatenation and interleaving. Section 7 gives the
  contextual result, §8 lists command laws, and §10 extends the model to
  fairness. The earlier LICS 1993 version gives the finite definitions in
  §5 and the partial-correctness contextual result in §6.
  [Journal DOI][brookes-doi] · [Author's journal scan][brookes-pdf] ·
  [Author's LICS version][brookes-lics]
- Yotam Dvir, Ohad Kammar, Ori Lahav, and Gordon D. Plotkin,
  *Two-sorted algebraic decompositions of Brookes’s shared-state denotational
  semantics*, FoSSaCS 2025, 377–398. Section 6.1 has the single-sorted carrier
  `(S × S)⁺ × X`, the two deductions, the identity-transition return and
  Kleisli extension by closed concatenation. Section 3.1 specifies finite
  Boolean stores and countable nondeterminism, and §5 defines the countable
  closed powerset used by the representation. Lean uses arbitrary store and
  result types and all closed predicates, allowing uncountable behaviors. It
  formalizes the single-sorted operations and their laws. The paper's
  hold/cede sorts and free-algebra representation are outside this fragment.
  [DOI][two-sorted-doi] · [arXiv v3, §6.1][two-sorted]

| Source construction | Lean contract |
| --- | --- |
| Nonempty sequence of state pairs | `Transition Store` is `Store × Store`. An accepted `Trace Store` is a nonempty list of these pairs. Each pair can summarize a program segment in which the environment does not intervene. Two consecutive pairs can disagree where the environment can act. |
| Stuttering and mumbling | `Rewrite.stutter` inserts `(s,s)` at any boundary, including the ends. `Rewrite.mumble` replaces consecutive `(s,t),(t,u)` by `(s,u)`. `Reduces` orients both deductions forward. `close` keeps the terminal result fixed and is extensive, monotone, idempotent and least among stable supersets. Raw words include the empty list for contexts. `Behavior.generate` first restricts to nonempty seeds, and no behavior accepts the empty word. |
| Return and Kleisli extension | `Behavior.ret x` closes the singleton identity words at every store, tagged with `x`. `Behavior.bind p k` closes concatenation of a word of `p` returning `x` with a word of `k x`, preserving the latter's result. Store equality is unnecessary at the join. `ret_bind`, `bind_ret`, and `bind_assoc` hold on the entire Lean carrier. The unit proofs insert an identity matching the first or last transition and then mumble across the join. |
| Returnless commands | `Command Store` is the unit-result carrier. `skip` is unit return, `seq` is constant-continuation bind, and `parallel` closes all order-preserving shuffles of the operands. Parallel is commutative with unit `skip`, and every sequential trace is also a parallel trace. `parallel_generate` permits shuffling nonempty seeds before either operand is closed. |
| One-transition clauses | `Behavior.atomic` accepts the closure of singleton words satisfying a store-pair/value relation. `atomic_completes_iff` recovers that exact relation on singleton observations. This is the generic form of the source's atomic clauses. |

The primary PDF bytes used here have these SHA-256 hashes.

| Artifact | SHA-256 |
| --- | --- |
| [Brookes journal scan][brookes-pdf] | `3899a77e5d500546dffff5eeb4743b6022c09f5f75e9d9c68f2c36c34e664cc4` |
| [Brookes LICS manuscript][brookes-lics] | `b3882f7c8b2a6cd375adc97654f19b62fa03f0ebceecefac411aecf28ac28d2d` |
| [Dvir et al., arXiv v3][two-sorted] | `76eb127b724d37dd09f10b63b0ad780c135abba681a2266abaab80d5d49bda98` |

## Scheduling and observations

- `Behavior.accepts trace result` observes the whole open word and its
  terminal value. The set may be empty, and membership describes a possible
  completed execution. `Behavior.forget` existentially hides the terminal
  value and retains all pairs and boundaries. It commutes with sequencing a
  constant continuation by `forget_bind_const`. A continuation that examines
  the value must select its behavior before that value is hidden.
- `Behavior.completes s t result` observes the singleton `[(s,t)]`.
  This is Brookes's §6 initial/final-store observation with a terminal value
  added. For generated behaviors, `completes_generate_iff` says exactly
  that a nonempty seed runs contiguously on one store from `s` to `t`.
  `seq_completes_iff` composes these observations by matching the middle
  store. The singleton observation discards the other boundaries and cannot
  recover the open words or the source's separate state-trace observations.
- A `Shuffle` chooses one operand's next segment at a time, preserving both
  local orders on a shared store. The open merged word can still contain
  gaps that a further environment could fill. `parallel_completes_iff`
  characterizes a singleton observation by a shuffle whose adjacent stores
  agree throughout. In the regression, the left word `[(0,1),(2,3)]`
  cannot execute alone on one store. A right-hand `(1,2)` can run between
  its segments and produce the singleton observation `(0,3)` under parallel
  composition. Sequencing the same two operands cannot produce it.
- The carrier is the finite completed fragment. It describes neither
  prefixes of unfinished execution nor divergence, deadlock, fairness,
  infinite observations, or terminal markers within a trace. Brookes's
  contextual full-abstraction result uses a defined command language,
  an operational semantics, and contexts able to test and set stores.
  The core proves trace laws and schedule correspondences. It makes no
  full-abstraction or operational adequacy claim for any language or runtime.

## Reproduce the checks

The [regression module][regression] is selected by the existing proof-region
Lake glob. It checks both units on a gapped behavior, result-dependent bind,
directional stuttering, matching and mismatched sequential joins, and a
shared-store observation that requires interleaving.

```sh
lake build --wfail +Silmaril.Semantics.Brookes.Defs \
  +Silmaril.Semantics.Brookes.Thms +Silmaril.Proofs.Semantics.Brookes.Regression
make check CHECK_TARGETS='+Silmaril.Semantics.Brookes.Defs +Silmaril.Semantics.Brookes.Thms +Silmaril.Proofs.Semantics.Brookes.Regression'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/semantics/brookes/Axioms.lean
```

The [audit][axioms] prints the transitive axioms of the public definitions and
theorem statements. The repository policy admits only `propext`,
`Classical.choice`, and `Quot.sound` for this topic.

[thms]: ../../Silmaril/Semantics/Brookes/Thms.lean
[regression]: ../../Silmaril/Proofs/Semantics/Brookes/Regression.lean
[axioms]: ../../tests/semantics/brookes/Axioms.lean
[brookes-doi]: https://doi.org/10.1006/inco.1996.0056
[brookes-pdf]: https://www.cs.cmu.edu/~brookes/papers/FullAbstractionSharedVariable.pdf
[brookes-lics]: https://www.cs.cmu.edu/~brookes/papers/lics93final.pdf
[two-sorted-doi]: https://doi.org/10.1007/978-3-031-90897-2_18
[two-sorted]: https://arxiv.org/pdf/2501.15104v3
[interaction]: https://github.com/hiloopai/silmaril-lean/pull/3543
[primitive]: https://github.com/hiloopai/silmaril-lean/pull/3539
[projection]: https://github.com/hiloopai/silmaril-lean/pull/3559
