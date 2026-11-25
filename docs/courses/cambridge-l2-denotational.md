# Pure CBV L2 denotation

This slice follows Peter Sewell’s Cambridge Part IB *Semantics of
Programming Languages* notes for 2025–26, dated 12 February 2026. It uses
the CBV application rules on p. 55, strict `let` on p. 60, and the
corresponding rules in the collected definition on pp. 65–67. The PDF
matches the SHA-256 for `sewell2026semantics`. [Notes][notes] · [Bibliography][bib]

```sh
lake build --wfail +Silmaril.Courses.Cambridge.L2.Denotational
```

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

## Extension to effectful and recursive L2

The normalization discussion on p. 59 precedes the introduction of recursive
functions. Section 4.4 includes `let rec` at function types, with the
recursive closure rule on p. 61. This total interpretation covers the pure
fragment above and makes no full-L2 coverage claim.

For store effects and loops, computations can use
`Comp A := Store → Part (A × Store)`. At a function type, a value can
map an argument value to a computation, so creating a closure and applying
it have separate meanings. The repository's Elgot instance for `Part`
provides iteration for while loops. Recursive function calls also need a
fixed point for the argument-to-computation function captured by `let rec`,
together with an adequacy proof for L2's existing `Expr.recClosure` rule. The executable
`RuntimeValue.recursive` closure provides a reference for the environment
layout. The pure interpretation uses total functions.
[Recursive-function rules][recursion] · [Elgot partiality][elgot] · [L2 closure interpreter][closures]

[notes]: https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=55
[recursion]: https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=61
[bib]: ../../references.bib
[elgot]: ../../Silmaril/Semantics/ElgotMonads/Thms.lean
[closures]: ../../Silmaril/Courses/Cambridge/L2/ClosureInterpreter.lean
