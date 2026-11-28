# Ordered parallel composition over LetIter

Silmaril's native exact LetIter interprets a typed term as an arrow
`J(R) → J(A)` in a strong Elgot Freyd model. Here `R` is the product
of the free and bound environments, and `A` is the interpreted result
type. The ordinary pair runs its left computation before its right
computation. Binding uses `extend` to retain a copy of the input values,
and looping uses `contextualLoop` to thread those values through an Elgot
body whose left summand returns and whose right summand recurs. A
parallel pair can use the same values and result product while admitting
both orders of independent effects. [LetIter interpretation][letiter] ·
[Shared constructors][constructors] · [Elgot interface][elgot]

The [interchange header][lean] checks two general claims in Lean.
Bifunctorial composition for the existing premonoidal tensor identifies
its two sequential schedules. A compatible lax parallel operation admits
both schedules. The [ordered Freyd API][ordered] checks the shared-context
construction. The [mixed categorical evaluator][evaluator] and the
[finite Brookes interpretation][brookes-model] check different routes to
LetParIter equation soundness.

## Ordered Freyd interface

Use left-to-right composition `f ; h` and write `J u` for a value arrow
mapped into the computation category. Start with the value products and
computation whiskers of a Freyd model. The LetIter interpreter additionally
uses its coproduct comparisons and chosen strong Elgot iteration. Equip the
computation hom-sets with preorders. Monotonicity of ambient composition is
a separate hypothesis where needed. With that hypothesis the computation
category is locally preordered. Interpret `f ≤ g` as inclusion of
observations in the examples below.

Supply a binary operation `P` on computation arrows with the existing
tensor on objects. For `f : X → Y` and `g : U → V`, its result has type
`X ⊗ U → Y ⊗ V`. The ordered composition contract is

```text
P is monotone in both arrows
P(id_X, id_U) = id_(X ⊗ U)
P(f,g) ; P(h,k) ≤ P(f ; h, g ; k)
P(f,id_U) = f ▷ U                 P(id_X,g) = X ◁ g
```

These are the identity and composition comparisons of a normal lax
functor between locally preordered categories. The three-stage and
identity pastings agree because their endpoints agree and each hom
preorder has at most one comparison between any two arrows. The
identity equation also follows from either whisker equation and
functoriality of that whisker.

For the value-facing laws, let `j_XU : J(X) ⊗ J(U) ≅ J(X × U)` be the
chosen Freyd comparison. Use the transported operation on arrows
between interpreted value objects.

```text
f ⊠ g = j_XU⁻¹ ; P(f,g) ; j_YV
f : J(X) → J(Y)                  g : J(U) → J(V)
```

In Lean, `OrderedParallel.tensor` is already this transported `⊠`.
`tensor_id` and `tensor_maps` derive identity and pure product agreement.
`lax_comp` states staged-to-independent composition on the transported
arrows. To move this inequation across tensor isomorphisms, use monotonicity
of composition with the comparison maps.

Require the following equalities for the interfaces used by LetParIter.

- **Pure products.** `J u ⊠ J v = J(u × v)`, with the existing value
  products. For a compatible `P` this equation also follows from the
  whisker equations, the Freyd comparisons, and exact pure composition.
- **Exact pure stages.** The composition comparison is an equality
  when both arrows in the first stage are in the image of `J`, or when
  both arrows in the second stage are in that image. For instance,
  `(J u ⊠ J v) ; (f ⊠ g) = (J u ; f) ⊠ (J v ; g)`, and there is the
  corresponding equality for pure postcomposition. These conditions
  also identify `f ⊠ J v` and `J u ⊠ g` with the respective
  transported whiskered sequences. Factor into two stages with an identity
  in the other lane. Exact pure stages justify these factorizations. The
  two native sequential orders agree whenever either arrow is central.
  `FreydCategory.image_central` guarantees this for value maps `J u`.
  `IsCentral` quantifies over every partner in both tensor positions.
  Pure-stage exactness is a separate field about arrows in the image of
  `J`. Membership in the center alone supplies no such field for `⊠`.
- **Coherence.** The chosen value associator, symmetry and unitors,
  mapped by `J`, are natural for `⊠` on arbitrary computation arrows.
  For example,
  `((f ⊠ g) ⊠ h) ; J α_out = J α_in ; (f ⊠ (g ⊠ h))`.
  The symmetry equation is
  `(f ⊠ g) ; J swap_out = J swap_in ; (g ⊠ f)`. The left and right
  unit equations identify `id_(J 1) ⊠ f` and `f ⊠ id_(J 1)` with
  `f` under the respective pure unitors. The pentagon, triangle and
  symmetry coherence use the existing value equations and functoriality
  of `J`. State these laws after transport by `j`, or verify that
  the computation-level laws transport through the chosen comparison
  isomorphisms. For the latter route, exact composition with stages
  made of the chosen tensor and unit comparisons, their inverses and
  identities suffices, using the strong symmetric Freyd coherence.

These are extra hypotheses on a model. For instance, equipping the
unordered Kleisli model of an Elgot writer with the equality order
turns lax composition into equality. Independent writes to a
noncommutative log then obstruct such a `P`. The mixed evaluator also
checks `not_all_models_extend` using the native countermodel to let eta,
which rules out an ordered extension for that particular Freyd model
under any hom preorder. In ordered observation models the two schedules
can both be below a larger behavior. [Premonoidal whiskers and centrality][categories] ·
[Writer example in the SSA semantics, §5][ssa-source]

In detail, apply lax composition to
`(f,id_U);(id_Y,g)` and to `(id_X,g);(f,id_V)`. The whisker equations
give `leftTensor f g ≤ P(f,g)` and `rightTensor f g ≤ P(f,g)`.
The proof needs just those two comparisons and the whisker equations.
The Lean theorem is `sequentialTensors_le_of_lax`. Applying the same
factorizations to an ordinary bifunctor gives two equalities with
`P(f,g)` and forces the independent binds to commute.
`leftTensor_eq_rightTensor_of_interchange` checks this for the native
premonoidal tensor. The regression uses the two lemmas to derive
centrality under bifunctorial composition and schedule equality for
a compatible lax operation with the equality order.

## Sharing a value context

For independent branches `f : J(R) → J(A)` and `g : J(R) → J(B)`,
write `Δ_R : R → R × R` for the value diagonal. The parallel clause is

```text
share_R(f,g) = J Δ_R ; (f ⊠ g)
```

The diagonal supplies the same input **values** to the two branches.
The branch domains omit the other branch's result. Both results are
available only after the pair returns. Branch effects can interact
through a shared store. For a chosen interpretation
of the syntactic product, append the same result-type isomorphism
used by native LetIter. Monotonicity of the clause uses monotonicity of
precomposition by `J Δ_R` and, after this last transport, of postcomposition
by the result isomorphism. `OrderedParallel.par` implements `share_R`, and
`denotePar` appends the result comparison. Exact pure
precomposition and `Δ_R ∘ u = (u × u) ∘ Δ_S` give
`J u ; share_R(f,g) = share_S(J u ; f, J u ; g)` for
`u : S → R`. Pure product agreement makes `share_R(J u,J v)` the
value pairing of `u,v` mapped by `J`. With a pure unit branch, factor
the diagonal through the pure product with the terminal map and use
the relevant unitor. Swap and reassociation follow from the
corresponding coherences and the equality of the maps that duplicate
the input for each branch. These proofs use only the value diagonal,
pure-stage exactness and the displayed coherence.

The checked shared-context equations are `par_reindex`, `par_maps`,
`par_postmap`, `par_swap`, `par_assoc` and both `par_unit` laws. The
`denotePar` lemmas apply to pairs of native derivations. The Par constructor
of the mixed evaluator applies the same operation to arbitrary mixed
branches. [Shared-context API][ordered] · [Native branches][native-par] ·
[Mixed evaluator][evaluator]

### Retained input and guarded case

The mixed evaluator's `Laws` record exposes two additional arrow-level
diagrams. For `E f := J Δ_R ; (id_(J R) ⊠ f)` and
`ψ(r,(a,b)) = ((r,a),(r,b))`, the first is `extend_par`.

```text
share_R(E f, E g) = E(share_R(f,g)) ; J ψ
```

Here is a mathematical derivation using the displayed pure-stage and
coherence laws. Expand the left side and use pure precomposition to
collect the input diagonals as `r ↦ ((r,r),(r,r))`. The pure middle swap
moves the two identity lanes to the first product and `f,g` to the
second. Its input action fixes that diagonal. The input now factors as
`r ↦ (r,(r,r)) ↦ ((r,r),(r,r))`. Use exact pure precomposition and
postcomposition to slide that last duplication past `id ⊠ (f ⊠ g)`.
The remaining computation is `E(share_R(f,g))`. Duplicating the retained
value and undoing the middle swap gives `ψ`. For pure continuations
`u : R × A → A'` and `v : R × B → B'`, pure postcomposition yields

```text
share_R(E f ; J u, E g ; J v)
  = E(share_R(f,g)) ; J (ψ ; (u × v)).
```

The second diagram, `case_left`, moves a case with a pure scrutinee out
of one branch. In the value category let `s : R → A + B`. The pure map
`r ↦ (r,s(r))` selects from `R × (A + B)`. By distributivity, its two
injections have sources `R × A` and `R × B`. If `J` preserves this
coproduct, pair the copairing of the two arm denotations with the other
branch precomposed by the projection to `R`. Precomposing the pair with
each mapped injection reindexes both operands, by `par_reindex`. The
coproduct universal property identifies the two-arrow copairing, and
precomposing by `J` of the selection map gives the guarded diagram.
The right case follows by symmetry. The mixed Lean soundness API takes
`extend_par` and `case_left` explicitly and checks their use at the
actual typing witnesses. [Arrow-level laws][mixed-laws] ·
[Pure coproduct cocone][coproduct]

### Optional interchange rule for terms

A term theory can adopt the following directed rule for independent
continuations. The continuations `k : J(R × A) → J(A')` and
`l : J(R × B) → J(B')` may be effectful and may read the ambient
values and their own branch result.

```text
E(share_R(f,g)) ; J ψ ; (k ⊠ l)
  ≤ share_R(E f ; k, E g ; l).
```

Use the sharing identity to rewrite the left side as
`J Δ_R ; (E f ⊠ E g) ; (k ⊠ l)`. The lax composition comparison
and monotonicity of precomposition give the required inclusion. The
left side stages both first phases before either continuation. The
right side keeps only the local order within each branch. This
inequation is an optional semantic rule under the displayed hypotheses.
The checked generated LetParIter equivalence uses the pure tuple-map
and guarded case equalities. The two generic Lean lemmas in the
[interchange header][lean] concern the native sequential schedules.
The staged syntax rule above is a mathematical consequence of `extend_par`,
`lax_comp` and monotonicity of precomposition by `J Δ_R`.

### Preservation of LetIter

Use the original interpretations for the inherited constructors,
including sequential pair and `contextualLoop`. The whisker equations
give the same `retainLeft` and `extend` if written with an identity
operand. Induction on typing derivations gives equality of the old and new
denotations. Lean checks this in `denote_embed`, and
`denote_embed_nativeTyping` relates the two evaluators at the original
proof-relevant witnesses. The inherited iteration uses `contextualLoop`
with its existing strong Elgot laws. [Native clauses and mixed agreement][evaluator]

For the generated mixed equivalence, `sound_of_native` checks the closure
with `Laws`, purity of designated primitives, `CentralDiagonal` and
`FixedNativeSound`. `CentralDiagonal` concerns `J Δ_R` composed with the
inverse tensor comparison. Centrality of `J Δ_R` itself follows from
purity. Centrality after transport is a separate hypothesis and is used
for the recursive uniformity case. `FixedNativeSound` is soundness at
exactly the embedded proof-relevant endpoints. In the canonical
`Type` Kleisli interpretation `native_sound_of_type` discharges that
obligation, and `sound_of_type` checks the full mixed equivalence under
`OrderedParallel` and `Laws`. The older exact native theorem uses its
own typing-coherence and shared-tensor hypotheses. [Mixed closure][mixed-closure] ·
[Canonical Kleisli soundness][kleisli] · [Exact soundness][soundness]

Closing an inequation under all constructors also requires order laws
for copairing and iteration in the arguments where rewriting is allowed.
A comparison between separately iterated branches and a joint scheduler
body requires a separate iteration theorem.

## Trace model and evidence

On languages of finite words ordered by inclusion, let `·` be
concatenation and `∥` be shuffle. The common unit is the singleton
empty word. A first-stage shuffle of `a,b` followed by a second-stage
shuffle of `c,d` has left and right projections `ac,bd`, so
`(A∥B)·(C∥D) ⊆ (A·C)∥(B·D)`. With distinct letters `a,b`,
take `A={a}`, `D={b}` and both other languages the unit. The
right side contains `ba` and the left side contains only `ab`.
Monotonicity, associativity and the two unit laws make both products
monoidal on the inclusion poset. The common unit supplies identity
unit comparisons. All interchange pastings, including the
three-by-two, two-by-three and both sets of unit diagrams, have the
same endpoints and hence commute by thinness. This is a mathematical
normal duoidal structure with noninvertible interchange. In
Aguiar–Mahajan's notation `⋄ = ·` and `⋆ = ∥`. To match the same diagram
in Garner–López Franco's notation the language operations are `* = ·`
and `∘ = ∥`. Their separate finitary endofunctor example takes `∘` to
be functor composition and `*` to be Day convolution. Its comparison is
a natural transformation. For a construction on profunctors or relations,
one must likewise specify the carrier, both products and units, and
the naturality, associativity and unit diagrams. The ordered Freyd API
supplies a lax operation relative to categorical composition. A proof
of duoidality on a proposed carrier would need its two monoidal
structures and coherent comparisons in addition to the arrow equations.
Strong 2-monoidality in Aguiar–Mahajan requires invertible constraints,
which the strict trace inclusion precludes. Concurrent Kleene Algebra uses
the same orientation for exchange. Its downward-closed pomset model uses
subsumption of partial orders. The finite word argument above is a separate
construction. [Aguiar–Mahajan, §6.1 and Proposition
6.11][am] · [Garner–López Franco, §§2 and 5.2][glf] ·
[Hoare et al., publisher abstract][cka] · [Kappé et al., explicit
exchange and pomset model][kappe]

For Brookes transition traces the carrier consists of nonempty
words and the common unit is closed skip, generated by singleton
identity transitions. Closing each input before either product
has the same effect as closing just the product of the seeds.
Concatenation lifts deductions into prefix or suffix contexts.
For shuffle, remove an inserted identity at its labeled position
in the merged word, or expand a contracted transition into its
adjacent pair there. This reconstructs a raw shuffle followed by
a deduction. Induction and symmetry give two-sided stability.
It lets one strip intermediate closures, proving associativity
and descending directed interchange. An identity transition
shuffled with a nonempty word adds a stutter. Conversely choose
an identity at its initial store and contract it with the first
transition. The concatenation unit proofs use stuttering and matching
identities at the two ends. These unit equations and the descended
comparison give the same thin-category proof of normal duoidality
on closed command languages. [Brookes, journal §6][brookes] ·
[Dvir et al., §6.1][dvir] · [Brookes core closure laws][core]

For a Kleisli arrow over `Behavior Store`, take its fibers at each
input and returned value. Composition joins the closed concatenations
over intermediate results. Pointwise `P` shuffles the two trace
fibers and retains the result pair. Directed interchange includes
each left-hand summand in the corresponding right-hand summand.
Pure graphs have one result fiber of weight skip at each input.
Thus pure stages relabel fibers or precompose their inputs, and
shuffle's monotonicity and coherence give the interface above.
In particular this argument uses the open words, including their
possible store gaps. Copairing is monotone by cases. Iteration is
monotone in the body because bind is monotone in both arguments,
so induction gives monotonicity at each finite bound and the union
preserves it.

In the landed Lean trace model, `Behavior.interchange_inclusion` checks
the forward comparison with value-dependent continuations.
`Behavior.shared_store_interchange_strict` checks a singleton observation
from store `0` to `2` with result `(1,())` that admits the left write and
read before the right write. Staging both writes before the read excludes
that outcome. The iteration header checks `LawfulElgotMonad`,
`iterate_accepts_iff` for finite approximation and `iterate_strength`
for a pure context. These are checked results on the trace carrier.
The thin-category duoidal packaging above is a mathematical argument.
[Parallel laws and witness][brookes-par] · [Iteration laws][brookes-iter]

`Behavior.parallelPairing` supplies the monadic tuple interface, and
`BrookesLetParIter.sound` and `interpret_sound` specialize the generic
monadic equations to the finite two-thread, one-cell, one-mutex world.
They use the existing result-map and tuple laws and `LawfulElgotMonad`.
The stronger categorical interpretation uses a separate `OrderedParallel`
and its arrow-level premises. The fiber argument above describes how
closed shuffle gives that operation. The concrete checked Brookes
instantiation uses `ParallelPairing`, and a packaged Brookes
`OrderedParallel` instance is outside these headers. The maintained
categorical regressions exercise the categorical route.
[Brookes instantiation][brookes-model] ·
[Monadic pairing contract][generic] · [Categorical regression][mixed-regression]

The Brookes carrier observes finite possible completions. Contextual full
abstraction, fairness and operational adequacy for a full SC scheduler
require separate results. [Brookes, journal §§7 and 10][brookes] ·
[Finite Brookes core guide](sc-brookes.md)

Check the two generic Lean consequences and their regression with

```sh
lake build --wfail +Silmaril.Semantics.Categories.Premonoidal.Interchange.Thms
make check CHECK_TARGETS='+Silmaril.Proofs.Semantics.Categories.Premonoidal.Interchange.Regression'
```

[lean]: ../../Silmaril/Semantics/Categories/Premonoidal/Interchange/Thms.lean
[letiter]: ../../Silmaril/SSA/Isotope/LetIter/Categorical/Thms.lean
[constructors]: ../../Silmaril/Raw/SSA/Isotope/LetIter/ProofRelevant/Semantics/Categorical.lean
[categories]: ../../Silmaril/Semantics/Categories/Thms.lean
[elgot]: ../../Silmaril/Raw/Semantics/Categories/Freyd/Elgot.lean
[coproduct]: ../../Silmaril/Raw/Semantics/Categories/Freyd/Distributive.lean
[soundness]: ../../Silmaril/SSA/Isotope/LetIter/Categorical/Soundness/Thms.lean
[core]: ../../Silmaril/Semantics/Brookes/Thms.lean
[brookes-iter]: ../../Silmaril/Semantics/Brookes/Iteration/Thms.lean
[brookes-par]: ../../Silmaril/Semantics/Brookes/Parallel/Thms.lean
[generic]: ../../Silmaril/Semantics/Elgot/Parallel/Defs.lean
[ssa-source]: https://arxiv.org/abs/2411.09347v2
[am]: https://pi.math.cornell.edu/~maguiar/a.pdf
[glf]: https://arxiv.org/abs/1507.08710v2
[cka]: https://link.springer.com/chapter/10.1007/978-3-642-04081-8_27
[kappe]: https://arxiv.org/abs/1710.02787v3
[brookes]: https://www.cs.cmu.edu/~brookes/papers/FullAbstractionSharedVariable.pdf
[dvir]: https://arxiv.org/abs/2501.15104v3
[ordered]: ../../Silmaril/Semantics/Categories/Freyd/Parallel/Thms.lean
[native-par]: ../../Silmaril/SSA/Isotope/LetIter/Categorical/Parallel/Thms.lean
[evaluator]: ../../Silmaril/SSA/Isotope/LetParIter/Categorical/Thms.lean
[mixed-laws]: ../../Silmaril/SSA/Isotope/LetParIter/Categorical/Laws/Defs.lean
[mixed-closure]: ../../Silmaril/SSA/Isotope/LetParIter/Categorical/Soundness/Thms.lean
[kleisli]: ../../Silmaril/SSA/Isotope/LetParIter/Categorical/Kleisli/Thms.lean
[mixed-regression]: ../../Silmaril/Proofs/SSA/Isotope/LetParIter/Regression/Terms.lean
[brookes-model]: brookes-letpariter.md
