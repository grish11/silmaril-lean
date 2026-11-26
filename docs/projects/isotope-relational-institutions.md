# Relational institutions for the sequential Isotope tiers

Import `Silmaril.SSA.Isotope.Institution.Relational.Thms`. The three room
functors are `Silmaril.Isotope.Institution.Relational.{LetSeq,LetCase,LetIter}.institution`.
Their covariant sentence functors and contravariant model functors are the
projections `Silmaril.Logic.Institution.sentenceFunctor` and `modelFunctor`.

## Reuse of the existing institutions

The relational interpretation uses the same sentence type and forward sentence
functor as the existing exact equational institution in each tier.
`Program` is the corresponding `Models.Carrier`, and `Program.translate`
is the existing `PresSig.translate` fold. The checked `sentenceFunctor_eq`
theorems identify these functors, including their action on arrows. For LetCase
the exact API comes through `Silmaril.SSA.Isotope.Institution.LetCase.Thms`,
which re-exports `Silmaril.Raw.SSA.Isotope.Institution.LetCase`.
Its `inst`, `pres`, and equational entailment results keep their published
names and algebra-model semantics. [Exact LetCase header](../../Silmaril/SSA/Isotope/Institution/LetCase/Thms.lean)

- `Observational.Thms` supplies the existing behavioral observations and
  orders for LetCase, LetIter and λSSA, including faults and divergence.
  Comparisons that need those observations should use this API and show
  how each observed behavior projects to a successful typed result.
  [Observational header](../../Silmaril/SSA/Isotope/Institution/Observational/Thms.lean)
- `Ordered.Thms` supplies the ordered refinement institution and the exact
  operation maps for LetCase and LetIter. The relational model arrows here
  compare interpretations by inclusion of primitive results. Connecting that
  order to the ordered presentation requires an interpretation on carriers
  and a proof for the requested refinement theory.
  [Ordered header](../../Silmaril/SSA/Isotope/Institution/Ordered/Thms.lean)
- `UndefinedBehaviour.Thms` provides the free nullary extension of presented
  signatures. An extension with explicit UB can use its signature operations
  and must supply the observation of the new symbol in the chosen model.
  [UndefinedBehaviour header](../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/Thms.lean)

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
construction. The inherited exact sentence functor fixes the free context
and uses the same universe for types, effects and free names. Bound contexts
and result types vary by sentence.

The exact sentence retains both native terms and their data-valued derivations
at a common `TypingIndex τ`. The proof of evaluation under reduct computes the
existing fold on those derivations. The primitive clause transports its source
and result along the equalities of the signature map.

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

## Parallel interface plan

The shared pieces are the existing `InstrSig` category, the exact judgment
index, the room interface and the shape of the evaluation/reduct theorem.
The sequential relational model functors are equal on the common value
structure by `letSeq_modelFunctor_eq_letCase` and
`letCase_modelFunctor_eq_letIter`. Their result observations give a baseline
for a comparison after a parallel tier chooses an observation and proves
agreement on the sequential embedding.

The lower observation-institution draft exposes the same `InstrSig` through
`Silmaril.SSA.Isotope.Institution.InstrSig.Thms`. For the cross-tier comparison,
take the two exact derivations from the sequential sentence and supply them
directly to the lower `ofLetSeq` or `ofLetCase` inclusion. The lower model
arrows use `Cslib.IsMonadHom` and preserve primitive evaluation and parallel
pairing. Its inclusion satisfaction lemmas compare full computations at the
supplied witnesses. Comparing those computations with sequential successful
outcomes still requires agreement at the chosen observation.
[Lower institution draft](https://github.com/hiloopai/silmaril-lean/pull/3752)

- **LetPar and LetParCase.** `Parallel.Derivation.denote` takes
  `Semantics.InstructionModel D Φ m`, `Parallel.ParOp m`,
  `Parallel.Control tier D m`, `FreeEnv D Γ` and `BoundEnv D β`.
  Products and unit come from the corresponding value equivalences.
  `Control.seq` supplies no case or feedback operations.
  `Control.case` uses `CoproductModel D` and `EmptyModel D`, so a
  powerset comparison to the sequential relational models needs the latter
  when using this control. At fixed `D`, `m`, pairing and control, a reduct
  can transport primitive inputs and outputs as in this PR. An output
  preorder used to lift primitive refinement through evaluation must compose
  with the interpreter's bind and parallel pairing, and with feedback in the
  iteration tier. A `SetM` comparison can use
  `RelationModel.toSetModel` and the sequential evaluator's
  `denoteRelation_iff_mem`. Choosing a parallel pairing and proving its
  required laws are separate obligations. [#3695](https://github.com/hiloopai/silmaril-lean/pull/3695)
- **LetParIter.** The native evaluator takes
  `LetIter.ProofRelevant.Semantics.InstructionModel Φ τ ε m`, `TypeModel τ`,
  `CtxDen Γ`, `BoundDen β`, Elgot iteration and `Elgot.ParallelPairing m`.
  The instruction model includes both Kleisli evaluation and a pure function
  for each bottom-effect instruction, with an agreement law. A reduct in this
  profile reindexes both judgments and transports the bottom witness using
  effect preservation. A relational primitive model can be lifted to this
  powerset profile only with the required type-model data and a pure
  implementation for each bottom-effect label. Using the evaluator requires
  its monad and iteration operations. Using the equational soundness results
  additionally requires their stated lawfulness and coherence hypotheses.
  [#3715](https://github.com/hiloopai/silmaril-lean/pull/3715)

### Exact endpoints in the iteration tier

The lower `Parallel.Equiv` relates terms at a shared judgment and uses
proposition-valued `HasType` at its typed rule endpoints. The upper
`LetParIter.Equiv` relates two specific exact `Derivation` values.
Its `native` rule takes exact native LetIter derivations `da` and `db` and
requires `TypedEquiv.Related pureEff Γ (nativeTyping da) (nativeTyping db)`.
A comparison with a raw equation or quotient therefore requires a separate
bridge at the relevant typing witnesses, with the direction and hypotheses
stated for that comparison.
[Lower equation definition](https://github.com/hiloopai/silmaril-lean/blob/e4a9cc1725160ad9348917503328d0c31b733af0/Silmaril/SSA/Isotope/LetPar/Equations/Defs.lean)
[Upper equation definition at 0218a4ac](https://github.com/hiloopai/silmaril-lean/blob/0218a4ac2fb85e20d35b991a792336a8f53aec2e/Silmaril/SSA/Isotope/LetParIter/Equations/Defs.lean)

The native inclusion theorem `LetParIter.denote_embed` starts from an exact
`LetIter.LocallyNameless.Derivation` `d`. In the shared proof-relevant model,
with the selected pairing and native environments, it compares `derivation d`
with the native evaluator at `nativeTyping d`. Its hypotheses include the
native type and instruction models, subtyping, bottom effect, a monad and
Elgot iteration. The computation equality in `LetParIter.sound` concerns
related exact derivations at bottom purity and also assumes a lawful monad
and lawful Elgot iteration. A comparison with the sequential relation here
would additionally need the value-model, environment and observation
agreements for the chosen model.
[Native inclusion and soundness at 0218a4ac](https://github.com/hiloopai/silmaril-lean/blob/0218a4ac2fb85e20d35b991a792336a8f53aec2e/Silmaril/SSA/Isotope/LetParIter/Thms.lean)

The one-way adapter is already explicit in #3715's `LetParIter.interpret`.
It takes `D := TyDen`, exposes the native product and sum equivalences,
transports unit and empty using `Unit ≃ PUnit` and `Empty ≃ PEmpty`, and
supplies `Elgot.iter` as the loop control. Its instruction argument is
`⟨denoteInstr⟩`. The projection uses the Kleisli field, so any reverse
construction must separately supply the pure field and agreement and the
type model's coercions. Proof-relevant coercion-bearing terms also need a
typing or denotation comparison with explicit coercion transport. [Adapter at the inspected head](https://github.com/hiloopai/silmaril-lean/blob/cacdfa0ac3bb333b7d5e351d2835c71867f3a4b4/Silmaril/SSA/Isotope/LetParIter/Shared/Defs.lean)

For environments, the adapter uses `CtxDen.lookup` and `BoundDen.get`.
The bound projection has the evident inverse by recursion on the snoc
context. A full free environment includes anonymous and shadowed slots
that visible lookup omits. Extending every visible environment back to
`CtxDen` requires a value at each invisible slot, or a context restriction
that removes those slots. For example, a context consisting of one anonymous
empty slot has a visible environment and an empty full environment type.
With pointwise agreement at projected environments, visible-environment
validity implies full-environment validity. The converse requires coverage
of the visible valuations.

For a vertical comparison over shared signatures, check
`embed_T (translate f e) = translate f (embed_S e)` and naturality of the
model comparison with respect to reduct along `f`. Pointwise denotation
agreement gives a satisfaction equivalence when the environment comparison
covers the valuations on both sides. For a horizontal comparison, use the
image of `f` under the comparison's signature functor and preserve the
fixed structural operations and observation used by the adapter. These are
the components to compare when proving a square of institution morphisms or
comorphisms. The term, quotient and denotation squares are separate work.

The fixed index, forward relabelling, backward reduct and `Room` follow the
fixed-world SC institution design. The fixtures follow its concrete
instantiation by exercising native evaluation and truth-changing reducts.
This development uses the Isotope relational evaluator and model APIs.
[#3591](https://github.com/hiloopai/silmaril-lean/pull/3591)
[#3605](https://github.com/hiloopai/silmaril-lean/pull/3605)

## Regressions

`IsotopeRelationalInstitutionTests` builds open Boolean equations through the
public header. The examples exercise a nonidentity label swap, a one-label
signature inclusion, reducts on objects and arrows, case selection and a
LetIter run with feedback before return. All three equations hold in the
original model and fail after the swap reduct. The paired axiom audit checks transitive dependencies of
the institution modules, proofs and regressions.
