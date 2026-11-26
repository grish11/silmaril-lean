# ACL2 institutions for nonrecursive logical books

The fragment uses one logical value sort. User function symbols are package-qualified names in a
partial arity table. `Signature.resolve` checks a name at a requested arity, and `Term.app`
requires exactly that many arguments. Signature arrows include existing declarations at their
original names and arities. The fixed primitives are `nil`, `t`, `cons`, `car`, `cdr`,
`consp`, `equal` and `if`. A sentence asserts that its term evaluates to a value other than
`nil` under every assignment of its free variables. The model supplies total functions for the
declared symbols and a carrier with the stated laws for the primitives.

`ACL2.logic` pairs this semantics with an inductive derivation relation. Its rules include
equality, substitution, congruence, modus ponens, and computation laws for pairs, atoms and
conditionals. `ACL2.logic_sound` proves that each derivation preserves satisfaction. The
π-institution has named definition bodies in its signatures and treats their equations as
available hypotheses. Its arrows preserve those bodies under translation. Its semantic
comparison interprets the equations as restrictions on the models.

## Books and native admission

A checked `Event.defun` introduces a fresh name with a body scoped over the previous signature.
An `Event.defthm` introduces a fresh theorem name with a derivation from existing definitions and
theorems. It leaves the definition table intact. The raw `World` record also describes imported
snapshots. An imported theorem table needs a proof of `World.Valid` before it can be relied on
as a consequence of that snapshot's definitions.

A `Book W V` records its required input and its output world. `Book.includeBook` composes two
checked sequences at their common world. `Book.provable_include` preserves derivations and
`Book.extension` preserves named entries. `Book.checked` eliminates dependency on the named
theorem table, giving derivations from definitions alone for books started with a checked input.
`Book.valid` propagates semantic world validity.
`Book.expand` constructs model expansions by interpreting each new definition in a model of the
preceding events. Consequently `Book.entails_iff` gives semantic conservativity for input-world
statements.

`Standard.source` emits ACL2 events for already resolved names. The host supplies package setup,
native admissibility and certification. `Standard.Interface` describes those external
observations and the interpretation of logical values and calls. `Standard.Included` relates a
native include to a trace of the checked events. `Standard.Realizes` states the separate
obligations for names, definitions and recorded theorems. Given those obligations,
`Standard.Realizes.sound` and `Standard.Realizes.presentation_sound` transfer derivations to
the supplied interpretation. The interface does not infer realization from certification alone.

This fragment covers nonrecursive logic-mode definitions and checked theorem events. Recursive
admission, induction, the full primitive suite, the ACL2 reader and macro system, guards, local
events, encapsulation and the ACL2 prover are outside the Lean model. The native test uses stock
ACL2 to prove the emitted statements independently of the Lean derivations.
[ACL2 8.7 manual](https://www.cs.utexas.edu/users/moore/acl2/v8-7/combined-manual/index.html) ·
[ACL2 8.7 source](https://github.com/acl2/acl2/tree/bc6f4f49e81a0711214a8d91f0d06e0e084d2204)

## Typed graph declarations

Names in the table are relative to `Silmaril.Logic.ACL2`.

| Declaration | Type and direction |
| --- | --- |
| `inst` | Ordinary institution on arity signatures |
| `presentedInst` | Ordinary institution on signatures with definitions, with definition-satisfying models |
| `pi` and `piIns` | The syntactic π-institution in the comorphism and morphism diagram categories |
| `Equational.toEquational` | Institution morphism from `inst` to the registered `Institution.Examples.EQ.inst` (registry ID `logic.institution.examples.eq.inst`). Models go to their one-sort equational algebras. Equations over image signatures translate back to ACL2 `equal` statements. |
| `forgetDefinitions` | Institution morphism from `presentedInst` to `inst`. Models forget the defining constraints. Sentence translation is the identity on each underlying signature. |
| `piSound` | Forward diagram comorphism from `pi` to `Institution.semanticPi presentedInst`, with identity signature and sentence translations. |

## Reproduce the example

Build the public modules and emit the two checked example books, one for the definition and one
for its theorems. This also runs the Lean checks for arity rejection, named theorem retention and
existence of a model of the resulting book.

```sh
lake build --wfail +Silmaril.Logic.ACL2.Standard.Thms \
  +Silmaril.Logic.ACL2.Equational.Thms +Silmaril.Logic.ACL2.Books.Examples
acl2_example_dir=$(mktemp -d)
lake env lean -DautoImplicit=false -DwarningAsError=true \
  --run tests/acl2/BookSource.lean "$acl2_example_dir"
```

Run the following from the generated directory with an ACL2 8.7 executable on the path. The
theorem book's own `include-book` loads the certified definition book. ACL2 should certify both
books and report a successful include of the theorem book.

```sh
cd "$acl2_example_dir"
acl2 > certify.log 2>&1 <<'EOF_ACL2'
(certify-book "acl2-definitions" 0 nil)
:u
(certify-book "acl2-theorems" 0 nil)
(good-bye)
EOF_ACL2
test -f acl2-definitions.cert && test -f acl2-theorems.cert
acl2 > include.log 2>&1 <<'EOF_ACL2'
(include-book "acl2-theorems")
(good-bye)
EOF_ACL2
! grep -E 'ACL2 Error|HARD ACL2 ERROR|\*\*\*\*\*\*\*\* FAILED' certify.log include.log
```
