# CBV L2 denotations

This slice follows Peter Sewell’s Cambridge Part IB *Semantics of
Programming Languages* notes for 2025–26, dated 12 February 2026. It uses
the CBV application rules on p. 55, strict `let` on p. 60, and the
corresponding rules in the collected definition on pp. 65–67. The PDF
matches the SHA-256 for `sewell2026semantics`. [Notes][notes] · [Bibliography][bib]

```sh
lake build --wfail +Silmaril.Courses.Cambridge.L2.Denotational
```

## Pure fragment

`L2.PureDenotation.Term Γ e T` is a computational typing derivation for a
fragment of the existing `L2.Expr` AST. It admits integers, Booleans,
`skip`, addition, comparison, conditionals, sequencing, bound variables,
lambdas, application, and strict nonrecursive `let`. Its environment
contains one semantic value per bound variable, with the nearest
binder first. A lambda denotes a function that closes over this
environment. Application supplies the argument's denotation to that
function. The fragment has no free names, store operations, loops, or
recursive bindings.

| Lean result | Contract |
| --- | --- |
| `Term.hasType`, `Term.scoped`, `Term.closed` | The derivation embeds in L2 typing, has the indexed binder depth, and is closed at an empty environment. |
| `Term.adequate` | For a closed fragment term at `int`, `bool`, or `unit`, a finite L2 run ends in a value iff its result is the quoted denotation paired with the original store. |
| `Term.terminates`, `Term.not_diverges` | Every closed derivation has a finite CBV evaluation to a value and admits no infinite CBV trace. This includes functions. |

The proof relates semantic functions to substitution-based lambda values by
their behavior on related arguments. The beta calculation extends the
substitution that represents the saved environment. The two examples on
slide 140 return `12` and `6`. A separate strict-let example checks
lexical scope by shadowing a name after a closure has captured it.

## Mutable-store fragment

`L2.EffectfulDenotation.Term locations Γ e T` adds dereference and
assignment at locations declared in the existing L2 typing environment.
It interprets a computation as `StateT Store Part A`. A function value
maps an argument to a computation. The closure saves its lexical
environment. Application evaluates the function expression and then the
argument, threading the store through both before running the closure in
the resulting store. Assignment updates an existing location after
evaluating its right-hand side, as in the collected L2 rules.

| Lean result | Contract |
| --- | --- |
| `Term.hasType`, `Term.scoped`, `Term.closed` | Each derivation embeds in L2 typing and has the indexed binder depth. An empty lexical environment gives a closed expression. |
| `Term.terminates` | Every closed derivation, including at function types, reaches an L2 value from a store covering the declared locations. |
| `Term.adequate` | For a closed derivation at `int`, `bool`, or `unit` and a covering initial store, a configuration belongs to the denotational observation iff the existing substitution-based small-step semantics reaches it with a value. Both observations include the entire final store. |
| `sat_iff` | On the same admitted sources, atomic satisfaction agrees with `L2.OperationalInstitution.semantics.May` for the corresponding `.returned` configuration. |

The function clause of the adequacy relation quantifies over related
arguments and covering stores. The evaluation proof uses
`Step.preserves_coverage` to pass the store hypothesis along the
constructed reduction. The institutional comparison concerns finite
ground returns on these sources.

Slide 138's argument writes `2` before the body writes `1`. Its
denotation and institutional observation both return `skip` with
`l ↦ 1`. The lexical-capture example saves `!l = 3`, writes `5` in
the function operand, and increments the location to `7` in the
argument. The body adds the saved `3` to the current `7`, returning
`10` with `l ↦ 7`.

## Chapter 4 coverage

| Pinned material | Denotation coverage |
| --- | --- |
| CBV application and typing, §§4.2–4.3 | Checked in both fragments for the represented ground and function types. |
| Strict local definitions, §4.4, p. 60 | Checked in both fragments. |
| Integer store operations and inherited CBV rules, §4.6, pp. 65–67 | Checked in the mutable-store fragment for lookup, assignment, sequencing, conditionals, addition and comparison. |
| Recursive functions, §4.4, p. 61 | Remaining. A fixed point for recursive closure application needs a correspondence proof for the existing `Expr.recClosure` rule. |
| While, §4.6 | Remaining. The existing Elgot instance for `StateT Store Part` can express iteration that threads the store through guard and body. |
| Call by name and unrestricted reduction, §4.2 | Outside the CBV denotations. |

[Recursive-function rules][recursion] · [Elgot state and partiality][elgot]

[notes]: https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=55
[recursion]: https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=61
[bib]: ../../references.bib
[elgot]: ../../Silmaril/Semantics/ElgotMonads/Thms.lean
