# Generalized institutions study C2 — SAT valuations

A signature is a type of atoms `A` and a signature morphism is any function `f : A → B`.
A sentence `Problem A` is a conjunction of clauses, each a disjunction of signed atoms.
`Problem.rename` maps atoms and keeps their polarity. `reduct f v` precomposes a target
valuation with `f`. This is the renaming and reduct pattern of the existing
[classical propositional institution](../../Silmaril/Logic/Institution/Examples/Propositional.lean).
`Problem.ofCNF` reads the existing DIMACS CNF as a problem over `Nat`, with evaluation
preserved pointwise by `Problem.eval_ofCNF`. Thus existing SAT and UNSAT still quantify
existentially and universally, respectively, over total Boolean assignments.
[Definitions](../../Silmaril/Logic/SAT/Institution/Defs.lean)

## Compositional evaluation

| Models | Values | Connectives |
| --- | --- | --- |
| Total valuations `A → Bool` | true, false | Boolean operations |
| Partial valuations `A → Option Bool` | true, false, unknown (`none`) | Strong Kleene. Negation fixes unknown. A single false conjunct or true disjunct is decisive. |
| Evidence valuations `A → Evidence` | true only `(1,0)`, false only `(0,1)`, neither `(0,0)`, both `(1,1)` | Negation swaps the bits. Conjunction uses AND on support and OR on refutation. Disjunction uses OR on support and AND on refutation. |

The empty clause is false and the empty problem is true in each algebra. In the evidence
**truth order**, support increases and refutation decreases. Conjunction and disjunction
are meet and join (`Evidence.le_conj_iff`, `Evidence.disj_le_iff`). False only is bottom,
true only is top, and both and neither are incomparable. In the **information order**,
both bits increase, with neither at the bottom and both at the top. The strong Kleene
truth order is false < unknown < true. Its information order has unknown below both
definite values, which are incomparable. Both compositional evaluators are monotone in
their respective information orders.

`Problem.eval_rename`, `Problem.evalK3_rename` and `Problem.evalEvidence_rename` give exact
evaluation after translation and reduct for every atom map. `Problem.evalK3_total` and
`Problem.evalEvidence_total` give agreement on total assignments. `Problem.evalEvidence_ofK3`
gives agreement throughout the three-value fragment with at most one evidence bit set.
[Semantic theorems](../../Silmaril/Logic/SAT/Institution/Thms.lean)

## Total completions

A total completion agrees with every known atom. Filling missing atoms with false witnesses
`exists_completion`. `Problem.superEval_eq_some` characterizes a definite result by unanimity
among completions. `Problem.superEval_eq_none` characterizes unknown by a true completion and
a false completion. `Problem.superEval_total` gives agreement on total assignments, and
`Problem.evalK3_informationLE_superEval` says a definite compositional result survives
completion. Supervaluation here quantifies over total assignments to a strong Kleene partial
valuation. The four-valued evidence semantics also permits conflicting information.

Every target completion reduces to a source completion. By `completion_lifts_iff`, a source
completion lifts exactly when it assigns equal values to atoms identified by the map. A lift
uses the common value on each occupied fibre and fills missing values outside the image.
Consequently injections give equality (`Problem.superEval_rename_of_injective`). For arbitrary
maps, the target quantifies over a possibly smaller collection of reducts. Its result refines
the source in the information order (`Problem.superEval_rename_informationLE`).

For `p ∨ ¬q` with both atoms unknown, the source has a falsifying completion `p = false,
q = true` and a satisfying completion. Identifying the atoms rules out the falsifying
completion, so `p ∨ ¬p` is supertrue. Compositional evaluation of the renamed clause at the
unknown atom still gives unknown. [Checked counterexample](../../Silmaril/Logic/SAT/Institution/Examples.lean)

## Ordinary observations and consequence

A predicate on values yields an ordinary satisfaction relation when its truth is invariant
under translation and reduct. Exact value equality gives that condition for every predicate.
The ordinary bundles use discrete valuation categories and the existing `Room` API. The two
strong Kleene bundles observe truth and falsity separately. The two evidence bundles observe
support and refutation separately. An evidence value of `both` meets both predicates and
`neither` meets neither. For supervaluation, injections give the required equivalence. On all
maps, supertruth is only preserved from reduct to translation, as the identification example
shows. Superfalsity has the same limitation, with `p ∧ ¬q` becoming `p ∧ ¬p`.
[Ordinary bundles](../../Silmaril/Logic/SAT/Institution/Ordinary/Defs.lean)

In each bundle, `Room.Entails Γ F` quantifies over every valuation that meets the chosen
observation for every premise in `Γ`. Local evaluation produces one value at one model.
For example, entailment in the evidence refutation bundle takes refutation of all premises
as its hypothesis and asks for refutation of the conclusion. Global UNSAT of a CNF says
that every total valuation falsifies it. [Room consequence API](../../Silmaril/Logic/Institution/Room.lean)

Generalized-core integration is deferred. For terminology and background, see
[Many-Valued Logic](https://plato.stanford.edu/entries/logic-manyvalued/),
[Belnap, *A Useful Four-Valued Logic*](https://doi.org/10.1007/978-94-010-1161-7_2),
and [Fine, *Vagueness, Truth and Logic*](https://doi.org/10.1007/BF00485047).
