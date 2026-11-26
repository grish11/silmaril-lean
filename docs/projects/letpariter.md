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
Bifunctorial composition of the existing premonoidal tensor forces its
two sequential schedules to be equal. An operation with directed
composition and the same whiskers admits both schedules. The ordered
Freyd interface and its consequences below are mathematical. The
concrete Brookes theorems identified below are checked separately in
[#3702][brookes-pr].

## Ordered Freyd interface

Use left-to-right composition `f ; h` and write `J u` for a value arrow
mapped into the computation category. Start with the repository's
strong Elgot Freyd data, including the value products, computation
whiskers, coproduct comparisons, and chosen iteration. Equip each
computation hom-set with a preorder, with composition monotone in both
arguments. Interpret `f ≤ g` as inclusion of observations in the
examples below.

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

Require the following equalities for the interfaces used by LetParIter.

- **Pure products.** `J u ⊠ J v = J(u × v)`, with the existing value
  products. For a compatible `P` this equation also follows from the
  whisker equations, the Freyd comparisons, and exact pure composition.
- **Exact pure stages.** The composition comparison is an equality
  when both arrows in the first stage are in the image of `J), or when
  both arrows in the second stage are in that image. For instance,
  `(J u ⊠ J v) ; (f ⊠ g) = (J u ; f) ⊠ (J v ; g)`, and there is the
  corresponding equality for pure postcomposition. These conditions
  also identify `P(f,J v)` and `P(J u,g)` with the corresponding
  whiskered sequence. Factor each into two stages with an identity in
  the other lane to see this. Centrality identifies the two whiskered
  orders in these cases. Exact pure stages supply equalities for such
  factorizations. The required exactness is for the chosen pure
  arrows, including identities.
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
noncommutative log then obstruct such a `P`. With an ordered
observation model the two schedules can both be below a larger behavior
without agreeing. [Premonoidal whiskers and centrality][categories] ·
[Writer example in the SSA semantics, §5][ssa-source]

In detail, apply lax composition to
`(f,id_U);(id_Y,g)` and to `(id_X,g);(f,id_V)`. The whisker equations
give `leftTensor f g ≤ P(f,g)` and `rightTensor f g ≤ P(f,g)`.
The proof needs just those two comparisons and the whisker equations.
The Lean theorem is `sequentialTensors_le_of_lax`. Applying the same
factorizations to an ordinary bifunctor gives two equalities with
`P(f,g)` and forces the independent binds to commute.

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
used by native LetIter. The new clause is monotone. Exact pure
precomposition and `Δ_R ∘ u = (u × u) ∘ Δ_S` give
`J u ; share_R(f,g) = share_S(J u ; f, J u ; g)` for
`u : S → R`. Pure product agreement makes `share_R(J u,J v)` the
value pairing of `u,v` mapped by `J`. With a pure unit branch, factor
the diagonal through the pure product with the terminal map and use
the relevant unitor. Swap and reassociation follow from the
corresponding coherences and the equality of the maps that duplicate
the input for each branch. These proofs use only the value diagonal,
pure-stage exactness and the displayed coherence.

Pure result maps may also depend on the retained input. Write
`E f := J Δ_R ; (id_(J R) ⊠ f)` for the existing `extend`, and
let `ψ(r,(a,b)) = ((r,a),(r,b))` be the pure map of value products.
Then

```text
share_R(E f, E g) = E(share_R(f,g)) ; J ψ
```

To prove this, expand the left side. Exact pure precomposition combines
the diagonals into `r ↦ ((r,r),(r,r))), followed by
`(id ⊠ f) ⊠ (id ⊠ g)`. The pure symmetry and associators group the
two identity lanes together and the two computation lanes together.
Use `id ⊠ id = id` and factor the input map through
`r ↦ (r,(r,r))`, duplicating the retained `r` on the identity lanes.
Exact pure precomposition puts that last duplication immediately
before the final pure tuple rearrangement. Their composite is `ψ`.
The remaining computation is `id ⊠ (f ⊠ g)), which is the
expansion of `E(share_R(f,g))`. For pure continuations
`u : R × A → A'` and `v : R × B → B'`, exact pure postcomposition
then gives

```text
share_R(E f ; J u, E g ; J v)
  = E(share_R(f,g)) ; J (ψ ; (u × v)).
```

This proves the shape of the pure tuple-map equation for the shared
syntax. A pure case scrutinee similarly factors through a pure arrow
into the sum of the two extended contexts. The pure binary cocone
`J(X + Y)` has injections `J inl` and `J inr` because `J)
preserves coproducts. Value distributivity and coproduct preservation
give the coproduct cocone on products with the other branch's input.
To move parallel pairing across the resulting copairing, compare the
two composites after each injection. For example, restricting
`[f₀,f₁] ⊠ g` along `J inl ⊠ id` gives `f₀ ⊠ g` by
exact pure precomposition. The universal property gives the equality.
When the scrutinee extends an ambient context, precompose the unchanged
partner in each arm with the weakening projection. This is the
pure-scrutinee guard used by the shared case rules. [Shared par typing
and equations][letpar-pr] · [Pure coproduct cocone][coproduct]

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
inequation is an optional addition to the syntax. The generic
equational pairing interface uses pure maps, symmetry, associativity
and the unit. The effectful comparison comes from the additional
lax composition law.

### Preservation of LetIter

Use the original interpretations for the inherited constructors,
including sequential pair and `contextualLoop`. The whisker equations
give the same `retainLeft` and `extend` if written using `P) with an
identity. Hence an embedding that preserves the existing typing
constructors and context interpretations preserves the denotation
of inherited terms, `⟦embed d⟧_P = ⟦d⟧`, by induction on typing
derivations. The existing strong Elgot and pure-uniformity laws
still apply to their original
whiskering and iteration. This argument also applies to computations
constructed using the new clause as arguments of the same semantic
operators.

For exact equations on inherited terms, retain the hypotheses of
`denote_equiv_of_coherent_shared_tensor`: the central unit, shared
tensor comparisons, typing coherence and pure interpretations of
the designated instructions. The same separation applies to the
abort-extended soundness theorem. Soundness for a new typed congruence
requires checking its added schemes and its purity and substitution
lemmas. If inequations are closed under all constructors, the
computation copairing and iteration must also be monotone in the
arguments under which rewrites are allowed. These order laws are
additional to the ordinary coproduct and Elgot equations. A law
relating separately iterated branches to iteration of a joint
scheduler body would require a separate comparison for that body.
[Exact soundness hypotheses][soundness] · [Abort extension][abort]

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
Aguiar–Mahajan's notation `⋄ = ·` and `⋆ = ∥`. In
Garner–López Franco's notation `* = ·` and `∘ = ∥`. Their
finitary endofunctor example uses composition and Day convolution
on functors with natural transformations. These are structures
on languages or functors. The computation arrows above use the
directed lax comparison. [Aguiar–Mahajan, §6.1 and Proposition
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

At the pinned [#3702][brookes-pr] revision, the Lean header
`Silmaril.Semantics.Brookes.Iteration.Thms` includes
`Behavior.parallel_natural`, `parallel_symm`, `parallel_assoc`,
the pure-operand and unit laws, and the `LawfulElgotMonad` instance.
`iterate_accepts_iff` characterizes membership by a finite
approximation, and `iterate_strength` handles a pure context.
`Behavior.interchange_inclusion` checks the directed comparison
for result-dependent Kleisli continuations.
`Behavior.shared_store_interchange_strict` witnesses a singleton
observation from store `0` to `2` with result `(1,())` that admits
the left write and read before the right write. Staging the writes
before the read excludes that result. The checked pairing adapter
uses those pure-map and tuple laws. Its `PUnit` law follows from
`parallel_ret_right`, `mapResult_comp` and `bind_ret`. One
concrete syntax soundness instantiation at `Behavior Nat` can use
the read and two write primitives from that witness once the generic
typed soundness theorem is available. [Iteration laws][brookes-iter] ·
[Parallel laws and witness][brookes-par] · [Generic pairing contract][generic]

The Lean bridge from the abstract ordered Freyd contract to the new
syntax and the concrete syntax instantiation remain open. The Brookes
carrier observes finite possible completions. Contextual full
abstraction, fairness, and operational adequacy for a full SC scheduler
require separate results. [Brookes, journal §§7 and 10][brookes] ·
[Finite Brookes core guide](sc-brookes.md)

Check the two generic Lean consequences with

```sh
lake build --wfail +Silmaril.Semantics.Categories.Premonoidal.Interchange.Thms
make check CHECK_TARGETS='+Silmaril.Semantics.Categories.Premonoidal.Interchange.Thms'
```

[lean]: ../../Silmaril/Semantics/Categories/Premonoidal/Interchange/Thms.lean
[letiter]: ../../Silmaril/SSA/Isotope/LetIter/Categorical/Thms.lean
[constructors]: ../../Silmaril/Raw/SSA/Isotope/LetIter/ProofRelevant/Semantics/Categorical.lean
[categories]: ../../Silmaril/Semantics/Categories/Thms.lean
[elgot]: ../../Silmaril/Raw/Semantics/Categories/Freyd/Elgot.lean
[coproduct]: ../../Silmaril/Raw/Semantics/Categories/Freyd/Distributive.lean
[soundness]: ../../Silmaril/SSA/Isotope/LetIter/Categorical/Soundness/Thms.lean
[abort]: ../../Silmaril/SSA/Isotope/LetIter/Categorical/AbortSequence/Thms.lean
[core]: ../../Silmaril/Semantics/Brookes/Thms.lean
[letpar-pr]: https://github.com/hiloopai/silmaril-lean/pull/3695
[brookes-pr]: https://github.com/hiloopai/silmaril-lean/pull/3702
[brookes-iter]: https://github.com/hiloopai/silmaril-lean/blob/26c8bc210c58370d5f168f31421bd546c3f192a1/Silmaril/Semantics/Brookes/Iteration/Thms.lean
[brookes-par]: https://github.com/hiloopai/silmaril-lean/blob/26c8bc210c58370d5f168f31421bd546c3f192a1/Silmaril/Semantics/Brookes/Parallel/Thms.lean
[generic]: https://github.com/hiloopai/silmaril-lean/blob/3f83340976bd41c746c123ca832b2c8e834a09e1/Silmaril/Semantics/Elgot/Parallel/Defs.lean
[ssa-source]: https://arxiv.org/abs/2411.09347v2
[am]: https://pi.math.cornell.edu/~maguiar/a.pdf
[glf]: https://arxiv.org/abs/1507.08710v2
[cka]: https://link.springer.com/chapter/10.1007/978-3-642-04081-8_27
[kappe]: https://arxiv.org/abs/1710.02787v3
[brookes]: https://www.cs.cmu.edu/~brookes/papers/FullAbstractionSharedVariable.pdf
[dvir]: https://arxiv.org/abs/2501.15104v3
