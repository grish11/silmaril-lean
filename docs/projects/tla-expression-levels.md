# TLA+ expression levels

Import `Silmaril.Logic.Temporal.TLA.Resolution.Levels.Defs`. First resolve the
module graph, then call `Levels.check checkedRegistry externalLevels`. The
check visits every reachable module and every supported body, including unused
definitions. Success classifies syntax by level and records the constraints on
calls to first-order operators.

`Resolution.resolveWith .levelSyntax registry root` binds the additional syntax
used by intact HourClock and ACP_SB. The default `Resolution.resolve` uses the
core profile. The extra profile covers square and angle action brackets, ENABLED,
UNCHANGED, always, eventually, fairness, leads-to, and anonymous expression theorems
with no proof.
A theorem statement receives a level at its body site and does not introduce a
binding or evidence of a theorem.

[Level interface](../../Silmaril/Logic/Temporal/TLA/Resolution/Levels/Defs.lean) ·
[Binding paths](tla-module-resolution.md) · [Pinned HourClock fixture](../../tests/semantics/tla-parser/check.py)

## Levels and signatures

A `LevelTerm` is the maximum of a fixed floor and the levels of the formal
binding IDs in its dependency list. A nullary closed body has no dependencies.
A variable contributes state level. A rigid quantified or function binder and
a nullary CONSTANT contribute constant level. A declared first-order CONSTANT
operator takes the maximum of its argument levels. A definition's expression
formals start at constant level when checking the body and contribute
symbolically to the result and requirements.

| Syntax | Operand constraints and result |
| --- | --- |
| Prime | Operand at most state, result action, including when the operand is constant. |
| ENABLED and UNCHANGED | Operand at most action or state, respectively. The result is state or action, respectively. |
| Square and angle action brackets | Body at most action, subscript at most state, result action. |
| Always and eventually | Result temporal. An action operand requires a direct square bracket for always or a direct angle bracket for eventually. |
| Weak and strong fairness | Subscript at most state, action at most action, result temporal. |
| Leads-to | Both operands may be constant, state or temporal, result temporal. |
| Negation, logical binary operators and junction lists | Result is the operand maximum. Conjunction, disjunction, implication and equivalence reject a mix of action and temporal operands. |
| Equality, set operators, tuples, indexing, record selection, set maps, set filters and CHOOSE | Operands at most action, result is their maximum. |
| IF, CASE and record constructors | Operands up to temporal, result is their maximum. Record sets cap operands at action. |
| EXCEPT | Base, index arguments and right-hand sides at most action, result is their maximum. Each `@` joins the preceding updated base and its own selector. |
| Flexible quantifiers `\EE` and `\AA` | Bound names have state level. The body must have constant, state or temporal level. The result has temporal level. The non-action requirement survives substitution of formal arguments. |
| Rigid quantifiers and anonymous function constructors | Body up to temporal. Domains are at most action and contribute to the result maximum. A temporal quantified body additionally requires domains at most state. |

Named built-ins have explicit positional signatures. Their ceilings and
weights follow the pinned SANY table, with the additional structural checks
above. For flexible quantifiers, the pinned SANY table sets a temporal
ceiling on the operand and a fixed temporal result. The non-action condition
and the bound variable level follow the explicit rule in §17.2. For every
signature-only operator in the reachable graph, the caller
must supply an `ExternalSignature` keyed by its exact `BindingId`. It specifies
a result floor, a maximum for each argument, and whether each argument
contributes to the maximum. The checker validates the identity and arity of
each supplied signature. Attest the standard-library signatures against the
same artifacts used to build the registry. Parsed libraries instead get
summaries from their definitions. For example, the pinned parsed `Naturals`
defines both `+` and `..` with constant floors and two contributing operands
capped at action.

[Specifying Systems, §§16.2 and 17.2](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=340) ·
[Pinned SANY built-in table](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tla2sany/semantic/BuiltInOperators.java#L80) ·
[Pinned standard module](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tla2sany/StandardModules/Naturals.tla)

## Calls, LET and evaluator handoff

- `CheckedLevels.expressionAt site` returns the expression's `LevelTerm` at a
  resolver path. `CheckedLevels.operatorAt id` returns a declared operator's
  `OperatorSummary`, including a LET definition and any captured formals.
  Use `LevelTerm.eval` to supply actual levels for symbolic dependencies.
- `OperatorSummary.instantiate` substitutes positional actual levels into the
  result and the residual requirements. It preserves dependencies on captured
  formals. Use `Condition.holds` with levels for the remaining dependencies.
  `maxArgumentLevels` reports the independent upper bounds. Relational
  requirements, including the mixed action/temporal guard, remain in
  `requirements`. A failed source call includes its own site and the site
  where the requirement originated, including through an import.
- Every operand is checked, including operands whose levels contribute no
  weight. For example, `Ignore(x) == TRUE` can return level zero when given a
  legal action expression. `P(x) == x'` returns action level and constrains its
  actual to at most state. `Ignore(P(x))` keeps that constraint on `x`.
- The LET result is the body result. All local definitions are checked.
  Requirements on captured formals survive even if the local operator is
  unused, with its own local formals at the definition's constant baseline.
  Calls to that operator perform the full substitution. The implementation
  keeps summary bindings for inspection by identity, and name resolution
  restricts their visibility.
- Evaluators can select declarations using the checked levels and use the
  retained Surface syntax and reference tables for execution. The result
  does not supply a value interpretation, a temporal denotation, or a proof.

The level rules in *Specifying Systems* §17.2 apply to expressions after
resolving definitions. The checker preserves guarded applications across
first-order calls. In a scratch probe the pinned SANY frontend rejected
`v' /\ []v` for a variable `v` but accepted the same arguments passed through
`Mix(p,q) == p /\ q`. The checker rejects both. SANY also accepted an action-level
LET directly under always, because its check is guarded by semantic node
kind. The direct-bracket rule here rejects that case. Probes also confirmed
the constant-prime result, unused LET capture constraints, and the
bounded-quantifier restriction.

[Pinned SANY application checks](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tla2sany/semantic/OpApplNode.java#L1020) ·
[Pinned SANY LET level checking](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tla2sany/semantic/LetInNode.java#L114)

## Scope and checks

Operator-valued formals and applications are deferred at the level boundary,
including named, symbolic and lambda actuals. The level pass has no fallback
level for these cases. Nested modules, recursive and function-definition units,
proof steps, named theorems and assumptions, guarantees
and action composition remain outside the syntax profile. The separate
[INSTANCE profile](tla-module-instantiation.md) excludes flexible quantifiers and rejects fairness during replay. Proof-free
statement intake supplies only a level annotation. Terms are classified by level without
checking value domains or mathematical truth.

```sh
lake build --wfail +Silmaril.Logic.Temporal.TLA.Resolution.Examples \
  +Silmaril.Logic.Temporal.TLA.Resolution.Levels.Examples
```

The regressions check first-order term and constraint propagation, lexical
captures, explicit library signatures, diagnostic provenance, and HourClock
statement and definition levels using the pinned source's unit bodies. With
the intact pinned files, the classifications are state for `HCini`, action
for `HCnxt`, and temporal for `HC` and the theorem statement.
The [intact ACP_SB regression](tla-acp-sb-resolution.md) checks every unit and
the levels of all 38 operators.

[Lean regressions](../../Silmaril/Logic/Temporal/TLA/Resolution/Levels/Examples.lean)
