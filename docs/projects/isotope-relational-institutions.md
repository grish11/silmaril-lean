# Relational institutions for the sequential Isotope tiers

Import `Silmaril.SSA.Isotope.Institution.Relational.Thms`. The three room
functors are `Silmaril.Isotope.Institution.Relational.{LetSeq,LetCase,LetIter}.institution`.
Their covariant sentence functors and contravariant model functors are the
projections `Silmaril.Logic.Institution.sentenceFunctor` and `modelFunctor`.

## Signatures, programs and models

Each institution fixes a type index `τ`, an annotation index `ε`, a free-name
type with decidable equality, a free-variable context `Γ`, and an interpretation
`D : τ → Type`. It uses the existing `InstrSig τ ε` category. Arrows are functions
on primitive labels that preserve the source, result and effect annotation
exactly. They may rename, include or identify labels with the same profile.
Source and result preservation may be propositional. The derivation map and
model reduct transport along those equalities. Preserving the annotation uses
the native signature category and leaves the annotation available for later
effect-sensitive constructions.

With fixed `τ` and `D`, source and target judgments share the same free and
bound environments. Type-changing signature maps also change the context indices
and require a comparison of value interpretations that preserves the structural
operations used by evaluation. Those maps would require an indexed model
construction. The fixed free context follows the existing exact Isotope
institutions. Bound contexts and result types vary by sentence.

A sentence consists of two native terms with exact data-valued derivations at one
judgment index `TypingIndex τ`. `Program.translate` uses native `Tm.mapInstr`
for the syntax and transports the exact derivation. The program identity and
composition laws hold for the whole dependent pair, including its typing data.

A model is a native `Semantics.RelationModel` on `D`. A model arrow `M ⟶ N`
includes each relation of `M` in the corresponding relation of `N`. Identity is
reflexivity and composition is transitivity. Model arrows are proof-irrelevant.
The model reduct reindexes primitive relations on objects and reindexes the
inclusion proofs on arrows. `Model.reductFunctor_id` and
`Model.reductFunctor_comp` state equality of reduct functors. Relations can be
partial or nondeterministic, and effect annotations impose no purity, totality,
or commutation conditions on the relations in this institution.

## Observation and satisfaction

For each free and bound environment, the sentence is true if the native
evaluator gives the same set of successful results for the two derivations.
`denoteRelation_translate` compares the outcome predicate of a translated
derivation in a target model with the outcome predicate of the original
derivation in the reduct. Applying that theorem to both sides yields the
satisfaction condition.

| Tier | Type and value structure | Observation |
| --- | --- | --- |
| LetSeq | Products and unit, with corresponding value equivalences | Successful outcomes of primitives, let-binding, and product introduction and elimination |
| LetCase | All type formers, with product, unit and coproduct value equivalences | Successful outcomes include the branch selected by the scrutinee. Abort has no successful outcome. |
| LetIter | The LetCase structure | Successful outcomes of finite iterations. A left result returns and a right result feeds back. |

The direct relational abort clause requires no `EmptyModel D` instance. When a
comparison with the native powerset interpretation uses an empty-carrier
equivalence, it has the assumptions of `Derivation.denoteRelation_iff_mem`.
LetIter equality observes finite successful results and cannot distinguish
behaviors by divergence, failure, scheduling, or traces alone. Sentences
retain their supplied exact derivations. This construction makes no claim of
derivation independence, soundness of an entire equational presentation, or
completeness for a syntax quotient. The existing exact equational institutions
instead use algebras of a presented syntax and have their own entailment results.

## Extension points

The model category and its reduct functors are shared. The header proves
`letSeq_modelFunctor_eq_letCase` and `letCase_modelFunctor_eq_letIter` on the
common value structure. A later sequential or
parallel tier with the same model profile can reuse `InstrSig`, `Equation.map`,
`Model` and `Model.reductFunctor`. A tier with richer model objects can give its
own category and model reduct over the same signature category. In either case
the tier supplies a native typed program map and an evaluation/reduct comparison
for its chosen observation. Any extra laws needed to interpret parallel
composition belong to that tier's model profile.

For a vertical comparison over shared signatures, the sentence square has
shape `embed_T (translate f e) = translate f (embed_S e)`. The model square
commutes between the tier comparison and reduct along `f`; it is immediate at
the shared model profile. Pointwise denotation agreement gives the vertical
satisfaction equivalence. For a horizontal comparison that changes signatures,
the corresponding square uses the image of `f` under the comparison's
signature functor. These interfaces allow comparing the two composites by
their sentence and model components.

The fixed index, forward relabelling, backward reduct and `Room` follow the
fixed-world SC institution design. The fixtures follow its concrete
instantiation by exercising native evaluation and truth-changing reducts.
This development uses the Isotope relational evaluator and model APIs.
[#3591](https://github.com/hiloopai/silmaril-lean/pull/3591)
[#3605](https://github.com/hiloopai/silmaril-lean/pull/3605)

## Regressions

`IsotopeRelationalInstitutionTests` builds open Boolean equations through the
public header. The examples exercise a nonidentity label swap, an inclusion of a one-label
signature, reducts on model objects and arrows, case selection and a LetIter execution that feeds back
before returning. All three equations hold in the original model and fail
after the swap reduct. The paired axiom audit checks transitive dependencies of
the institution modules, proofs and regressions.
