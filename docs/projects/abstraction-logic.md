# Abstraction Logic

Import `Silmaril.Logic.Abstraction` for the core, deductive soundness and both comparisons.
It is also re-exported by `Silmaril.Logic`. The smaller imports are
`Silmaril.Logic.Abstraction.Thms`, `Silmaril.Logic.Abstraction.Soundness.Thms`,
`Silmaril.Logic.Abstraction.FirstOrder.Thms`, and
`Silmaril.Logic.Abstraction.Propositional.Thms`.

| API | Contract |
| --- | --- |
| `Shape`, `Signature.Hom` | A shape has a valence (the number of shared binder slots) and a subset of those slots for each argument. Every slot occurs in some argument. Symbol maps preserve the whole shape, including overlaps. |
| `Term S k`, `Template S n` | A term has `k` local parameters. Each abstraction argument appends its own slots in increasing slot order (`Shape.slot`). A template is a term whose local context consists of its `n` parameters. A free name and its arity together identify a schematic operation. |
| `Term.rename`, `Term.instantiate`, `Term.subst`, `Rule.subst` | Rename or instantiate local parameters, or simultaneously replace free schemata by templates. The nameless local context makes the operations capture-avoiding. `Term.eval_instantiate`, `Term.eval_subst` and `Rule.holdsAt_subst` describe their denotations. |
| `Algebra`, `LogicalOrder`, `ValuationSpace` | Each abstraction acts on a tuple of operations on a single nonempty carrier. The logical order is a complete lattice of truth values with a retraction from the carrier. Admissible valuations are nonempty and closed under nullary updates and syntactically definable substitutions. `ValuationSpace.full` is the unrestricted case. |
| `Rule`, `Model.Sat` | A sentence has finitely many premise templates and a conclusion with no dangling local parameters. At each admissible valuation, the meet of truth values of all premises over all their parameter tuples lies below the truth value of the conclusion. The empty premise list tests truth at the top of the lattice. |
| `Rule.map`, `Model.reduct`, `Model.satisfaction` | Translating symbols in a rule and evaluating it in the target is equivalent to evaluating it in the reduct. The reduct keeps the carrier, truth structure and admissible valuations. It is closed under source substitutions because they translate to target substitutions and commute with evaluation. |

The shapes `[{0}, {0}]` and `[{0}, {1}]` both pass two unary operations to the interpreter.
They have different valences and scope sets, which the signature retains. The locally indexed
representation identifies terms up to bound-name renaming. Premise lists are finite representatives
of sets. Reordering or duplicating them leaves satisfaction unchanged. The unrestricted
institution `Abstraction.inst` uses discrete model arrows and is registered as
`logic.abstraction.inst`.

## Derivability and soundness

`Derives theory Γ t` is the seven-rule calculus of the pinned Primer (Figure 4). The theory
is a set of rules, and `Rule.Derivable` uses the set of hypotheses from a sentence's premise list.
`Derives.finite` proves that antecedents of derivations are finite. `Rule.Derivable.sound` says
every model satisfying the theory satisfies the derived rule, with general admissible valuation
spaces. `Rule.Derivable.entails` states the result in the institutional room.

| Primer rule | Lean constructor | Meaning and side conditions |
| --- | --- | --- |
| Axiom | `Derives.axiom` | Use a rule in the theory. |
| Assume | `Derives.assume` | Conclude a term from that term as a nullary template premise. |
| Add | `Derives.add` | Add a premise to the antecedent. |
| Bind | `Derives.bind` | Reorder, add or remove a premise's outer parameters. Open the old and new templates with distinct names fresh for each template's free nullary occurrences. The opened bodies must agree, and each removed name must be unused in that body. |
| Subst | `Derives.subst` | Substitute schemata simultaneously in the antecedent and conclusion. The substitution/evaluation law and closure of admissible valuations justify this step. |
| VarElim | `Derives.varElim` | Drop a nullary variable premise whose name is absent at arity zero from the other premises and conclusion. Update that label to the carrier representative of top from `LogicalOrder`. |
| Infer | `Derives.infer` | Discharge a template premise with a derivation of its opened body. The distinct opening names are fresh for the template and the supplying premises at arity zero. Closure of admissible valuations under nullary update allows the supplying rule to be used at each parameter tuple. |

`Term.Fresh` tracks free nullary occurrences, and `Term.openWith` exposes local
parameters as nullary names. A schematic occurrence of the same name at positive arity
is independent of these names. The soundness proof uses §3.5 and Appendix C.

Obua's 2022 account hard-wires modus ponens and universal introduction into its proof
rules and semantics. The 2023 Practal note makes both theory rules and expresses the
premise of universal introduction as a template. The later Primer gives the
order-theoretic semantics and general rule calculus used here. Object-language
introductions and eliminations enter through the theory. Appendix L.2 gives universal
introduction and instantiation and derives existential elimination with a template
premise. The fixed-arity formalization covers nameless abstract syntax and semantic
soundness. Named Practal parsing and kernel correspondence, plural binders and completeness
are outside its verified scope.

## Checked comparisons

The canonical first-order profile, `FirstOrder.profileInst`, has Abstraction Logic rules
as sentences over translated signatures and admits canonical models indexed by nonempty
unsorted first-order (UFOL) structures. For a UFOL carrier `D`, the canonical algebra uses
`D ⊕ Bool`, with a two-valued truth classification and a universal abstraction that
ranges over the embedded object carrier `D`. This works even when `D` is a singleton.
The profile uses full valuation spaces.

| Graph record | Lean declaration | Sentence and model directions |
| --- | --- | --- |
| `logic.abstraction.first_order.from_ufol` | `FirstOrder.fromUFOL` | UFOL sentences translate to premise-free rules in the profile. Canonical profile models go back to their indexing UFOL structures. |
| `logic.abstraction.propositional.to_profile` | `Propositional.toProfile` | Propositional formulas translate via UFOL nullary predicates to profile sentences. Profile models go back to propositional valuations by reading those predicates. |
| `logic.abstraction.first_order.to_abstraction` | `FirstOrder.toAbstraction` | The profile-to-unrestricted morphism maps each profile model to its canonical abstraction model and reads unrestricted rules back unchanged at the corresponding signature. |

Both comparison comorphisms are model-expansive. Every UFOL structure indexes a
profile model, and every propositional valuation is represented by a profile model
built from a singleton UFOL structure. `FirstOrder.entails_iff` and
`Propositional.entails_iff` prove preservation and reflection of consequence for
their translations **in this profile**. `FirstOrder.sat_sentence` and
`Propositional.sat_sentence` state the corresponding truth equivalences.

`FirstOrder.entails_of_abstraction` goes from consequence over all unrestricted
abstraction models to UFOL consequence. The reverse implication fails for this
translation. In the checked countermodel, the carrier is `Unit ⊕ Bool` and every
abstraction returns false, including the symbol translating first-order truth.
The UFOL sentence `tt` is valid, but its translation fails in that unrestricted
model.

## Examples and checks

- `Regression.lean` exercises overlapping binder scopes, a nonbinding argument under an
  outer parameter, arity-zero updates, capture-avoiding substitution, rule validity, and a
  nonidentity signature map.
- `Soundness.lean` uses universal introduction and instantiation at a schematic term,
  then derives their consequence with `Infer`. It exercises freshness at different
  arities, binder permutation and removal, and countermodels to the quantifier rules.
- `Comparisons.lean` checks a nested quantifier formula on singleton and two-object
  structures, the unrestricted countermodel, and evaluation after a propositional
  variable collapse.

```sh
make check CHECK_TARGETS='+Silmaril.Logic.Abstraction +Silmaril.LogicGraph.Nodes.Logic.Abstraction.Defs'
lake build --wfail +Silmaril.Logic +Silmaril.LogicGraph.Audit.Defs SilmarilLogicGraphData
make logic-graph-check
```

## Primary sources

The sources below are by Steven Obua. Artifact versions and SHA-256 hashes are
pinned in [references.bib](../../references.bib).

- `obua-2021-abstraction-logic`, *Abstraction Logic*, version 2.
  See “Algebra”, “Syntax”, and “Semantics”. [Author's report](https://obua.com/publications/abstraction-logic/2/)
- `obua-2022-abstraction-logic-foundation`, *Abstraction Logic: A New Foundation for (Computer) Mathematics*.
  See §§3–5 and §§10–14 for shaped syntax and the earlier model and proof rules. [arXiv:2207.05610v1](https://arxiv.org/abs/2207.05610v1)
- `obua-2023-axioms-are-inference-rules` and `obua-2023-logic-is-algebra`.
  The former documents the Practal change, and the latter gives shared-slot syntax
  and a distinguished-truth rule semantics in §§4–9. [Practal note](https://practal.com/press/aair/1) · [arXiv:2304.00358v1](https://arxiv.org/abs/2304.00358v1)
- `obua-2026-abstraction-logic-primer`, *Abstraction Logic: A Complete Logic over Second-Order Abstract Syntax*,
  full version dated November 16, 2026. Section 3, “A Primer in Abstraction Logic”, gives
  the syntax, ordered semantics, and rules used here. [Versioned Zenodo record](https://doi.org/10.5281/zenodo.24276226)
