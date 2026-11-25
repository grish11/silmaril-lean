# TLA semantic kernel

Import [`Silmaril.Logic.Temporal.TLA.Kernel.Thms`](../../Silmaril/Logic/Temporal/TLA/Kernel/Thms.lean)
and use the namespace `Silmaril.Logic.Temporal.TLA.Kernel`. The kernel builds on
[scoped General TLA](tla.md#scoped-general-tla). Its two fixed scalar carriers
are Lean `Int` and `Bool`. An elaborator supplies a General TLA scope with
typed rigid and flexible names, a rigid environment, and flexible state
valuations.

## Building denotations

| Checked input | Kernel interface |
| --- | --- |
| Typed state term | `StateExpr Γ X` is definitionally `General.Expr Value Γ X`. Build constants and lookups with `Term.literal`, `Term.rigid` and `Term.flex`. |
| Typed step term | `StepExpr Γ X` reads one source and target pair under a shared rigid environment. Apply `Term.current` or `Term.next` to a whole state term to read it on the corresponding valuation. |
| Scalar operations | `Term.neg`, `add`, `sub` and `mul` use exact integer arithmetic. `Predicate.eq` uses same-carrier equality, and `lt` and `le` use integer order. `Term.ite` requires a decidable condition and branches of the same type. |
| Boolean operations | `Predicate.not`, `and`, `or`, `implies` and `iff` compose propositions and their decisions. `Predicate.ofBool` tests a Boolean term for truth, and `Predicate.check` returns a Boolean term from a predicate. |
| Bounded binder | `Term.enumeration` evaluates a finite list of terms in the outer environment. `Predicate.existsIn` and `forallIn` quantify over membership in that list. The body lives in `Γ.bindRigid a`. Use `Γ.rigid.fresh a` for the new name and `weakenRigid` to reuse outer terms and predicates. |

A list represents a finite quantifier domain by membership. The truth of a
quantifier is independent of order and duplicates. The domain can depend on
the current input, including either endpoint of a step. Every candidate
extends the same rigid environment for the entire body. Existential
quantification over the empty list is false and universal quantification
over it is true. The kernel gives no general TLA+ set denotation for lists.

`StatePredicate Γ` has one flexible valuation as input and converts to a
General TLA atom via `.toStatePred`. `StepPredicate Γ` has a source and target
valuation as input and converts to `General.Action` via `.toAction`. A state
predicate can be lifted with `Predicate.current` or `Predicate.next`. The
terms and predicates are Lean denotations. The checked representation adds
an executable `Decidable` witness to each predicate, with agreement given
by `Predicate.check_iff`. This lets a caller compose already checked
denotations directly.

Every conjunct in a step sees the **same** pair of valuations. For example,
`x' = y ∧ y' = x` constrains both target coordinates using source coordinates,
so a source pair `(0,1)` has target pair `(1,0)`. A target coordinate omitted
from an action can take any value consistent with its other constraints.
An unchanged clause is an explicit equality across the two valuations.

## Bounded graphs

Construct a `Bounded Γ Node` from a list of candidate nodes and a function
that decodes each node to a valuation. Give `Bounded.initials` and
`Bounded.transitions` the same rigid environment when evaluating a spec.
`Bounded.mem_initials` and `Bounded.mem_transitions` prove that the returned
lists contain exactly the listed states satisfying initialization and the
listed endpoint pairs satisfying the supplied action. The enumeration checks
every candidate pair, including pairs at states unreachable from
initialization. It uses the listed domain at both ends, so it does not
decide whether a state admits a successor outside the domain. Duplicate
nodes in the input can result in duplicates in the output.

Pass the raw predicate to enumerate its action. To enumerate `[A]_f`, pass
`A.bracket f` explicitly. This uses General TLA bracket semantics via
`Predicate.bracket_toAction`. If the observation is injective on states,
`Predicate.bracket_full` shows it admits precisely the raw steps and
whole-state self-loops. Temporal behaviors and fairness are handled by the
standalone TLA APIs.

The [Lean examples](../../Silmaril/Logic/Temporal/TLA/Kernel/Examples.lean)
construct predicates by hand. They check the full initial-state and raw
step lists from the [pinned Quint oracle](../../tests/semantics/tla-quint/oracle.json)
on 3 counter states and 4 bit-pair states. The raw counter has no successor
at `2` in the finite graph, and the explicit full-state bracket admits
`2 → 2`. BitPair exercises the existential Boolean choice and the
simultaneous use of the old integer coordinates.

```sh
lake build --wfail +Silmaril.Logic.Temporal.TLA.Kernel.Thms \
  +Silmaril.Logic.Temporal.TLA.Kernel.Examples
```

## Source elaboration handoff

The next step is to resolve imports, declarations, operator names and
arities, and locally bound names. The elaborator also needs to establish the
supported scalar and finite-domain types, check TLA+ expression levels and
the legality of priming, and lower the bodies and aliases of `q_init` and
`q_step` into the state and step interfaces. The domain of candidate
valuations remains an explicit exploration parameter. Source-level tests
can then feed the pinned exports through elaboration and compare the
resulting graphs with the same oracle.
[Export fixtures and provenance](../../tests/semantics/tla-quint/README.md)

In these modules, `:=` resolves to the Apalache infix definition
`__x := __e == __x = __e`. Elaborate the resolved operator as equality.
Priming on the left denotes evaluation in the target valuation, and the
unprimed expressions on the right use the source valuation. The kernel
has no assignment rule for the spelling `:=`.
[Pinned Apalache definition](https://github.com/apalache-mc/apalache/blob/7954daf7563a69cce9d0b89c8542e40bf46f7c6e/src/tla/Apalache.tla)

The checked agreement here is between the bounded evaluator and the Lean
denotations. Source parsing and module resolution, source-semantic
correctness, and general set-theoretic TLA+ semantics remain outside that
agreement.
