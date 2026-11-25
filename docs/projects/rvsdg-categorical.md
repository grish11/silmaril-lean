# Categorical denotations for RVSDG primitives and γ

The typed acyclic RVSDG fragment has two categorical interpretations.
`Term.denote` follows the let syntax and `Graph.denote` composes the numbered
vertex table directly. Each visits nested regions with fresh local scope.
`Graph.denoteOpen_toTerm` proves equality of arrows for every typed prefix.
`Graph.denote_toTerm` and `Term.denote_toGraph` cover whole regions with the
same recursive numbering. [Definitions][defs] · [Theorems][thms]

## Model and wiring

`Categorical.Model` uses the Cartesian value category of the repository's
λSSA Freyd setting. A value sort is assigned a value object, and a state sort
is assigned a snapshot object only when its data admits the same copy and
discard rules. Each primitive has an arrow from its ordered input product to
its ordered output product in the value category. The product has port zero on
the left and the tensor unit at the right end. Local tuples are grouped by
producer in ascending node order, and arguments are the left factor of the
whole environment. Wires are projections from that environment assembled in
user-port order. Repeated users take the same projection and unused origins
are dropped through the product structure.

The binder pairs the environment identity with the arrow for the node, then
uses associators and unitors to append its result tuple to the local scope.
`Categorical.freyd_bind_map` identifies this pairing followed by any pure
continuation with the actual λSSA binder on the mapped arrows. The proof
uses the strong premonoidal functor's tensor isomorphism and its naturality.
`FreydCategory.image_central` applies to each mapped arrow. The receiver of a
γ payload is scoped to the arm's arguments. The surrounding scope is carried
by the outer binder, and the arm can access only the supplied payload.
[λSSA categorical definitions][lambdassa] · [Freyd and Elgot interfaces][freyd]

For each arity `n`, `Selectors` gives an object `Kₙ` and tags
`tag i : I → Kₙ` indexed by `Fin n`. For every payload object `X`, it gives
the coproduct witness for `Kₙ ⊗ X` with legs
`⟨!ₓ ; tag i, idₓ⟩ : X → Kₙ ⊗ X`. This is the finite right-distributor
interface at the selector object, with the inverse implicit in the coproduct
universal property. Dispatch is the unique copair of the arms out of that
cocone. `dispatch_leg` recovers exactly arm `i` on leg `i`, and
`freyd_dispatch_map` proves that the coproduct-preserving value functor
carries the dispatch to the copair of the mapped arms.

A symmetric monoidal tensor alone supplies the permutations, regroupings and
unitors of an ordered wiring. General fan-out and unused wires additionally
require legal copy and discard maps on the affected objects. For wiring
independent of a chosen copying tree, these maps should be coherent
cocommutative comonoids where admitted, with a tensor-compatible choice on
copyable contexts. This implementation uses the stronger Cartesian value
structure and its canonical diagonals and deletions throughout. In particular,
state snapshots here model ordinary data such as histories. Linear runtime
resources and general ordered effects are outside the admitted model.

## Operational specialization

`Categorical.Model.ofRuntime` interprets a total deterministic RVSDG model
in the Cartesian category of types. A selector is `ULift (Fin n)` and a
primitive arrow decodes its input tuple and encodes its operational result.
Every other arrow is constructed by categorical wiring, composition or
copairing. The `pack` and `unpack` inverse laws identify all points of the
tuple product with typed runtime tuples. `Term.denote_pack` and
`Graph.denote_pack` identify the complete returned tuple, including returned
snapshots, for every input. These theorems concern fixed numbered regions and
total deterministic primitive models. Scheduling invariance, fault and
divergence observations, and Petri firing semantics are separate results.
[Base syntax and operational semantics][base]

## Follow-on work

- For θ, interpret the body as an arrow from the loop tuple `X` to
  `K₂ ⊗ X`. In the computation category, use the two tagged legs to route
  the updated tuple into the left summand of `X ⨿ X` on stop and the right
  summand on continue. Apply `Iteration.iterate` to the composite. The
  Elgot fixpoint equation unfolds the first
  body step. An invariant capture would use the existing contextual strength
  law. A separate adequacy theorem should relate finite returns and
  divergence to the chosen operational observations.
- For the SSA bridge, start with exactly typed, single-exit open regions and
  match the ordered input, result and opcode signatures. Specify a relation
  for each direction and prove typing and common-observation preservation
  for every related pair. Construct each admitted translation as a dependent
  pair of its target and a witness of the relation, so each direction
  inhabits its translation fibre. In the RVSDG-to-SSA direction, use local
  numbering to introduce lets and ordered arms to introduce cases. In the
  reverse direction, relate SSA lookups to typed origins and make captures
  explicit at each region boundary. Extend the observation to state and
  divergence together with the corresponding syntax and semantics.
- For a dialect institution, use signature-preserving opcode maps, sentence
  relabelling, and model reducts. Prove that interpretation commutes with
  relabelling and reduct before packaging satisfaction. The acyclic
  λSSA/λRTL institutions provide the opcode-renaming pattern. The Isotope
  observational institution provides the model for comparing behaviours,
  including returned state, faults and divergence.
  [SSA institution interfaces][institutions]

## Reproduce

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Categorical.Thms
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.Categorical.Thms
lake env leanchecker Silmaril.SSA.RVSDG.Categorical.Thms
```

## Sources

- Nico Reissmann, Jan Christian Meyer, Helge Bahmann and Magnus Själander,
  *RVSDG: An Intermediate Representation for Optimizing Compilers* (2020),
  arXiv:1912.05036v2, §§4, 4.1.1–4.1.3, 4.3, 5.1.2–5.1.3 and 5.2.2. PDF SHA-256
  `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
  [Versioned PDF](https://arxiv.org/pdf/1912.05036v2) · [DOI](https://doi.org/10.1145/3391902)
- Jad Ghalayini and Neel Krishnaswami, *The Denotational Semantics of SSA*
  (2024), arXiv:2411.09347v1, §§5.1 and 5.3, especially Definitions
  5.1 and 5.3–5.5. PDF SHA-256
  `5194f35c8375fc1c2ffd88d62bdf1c19d961894d1cc518ad68b5bb673b4f4114`.
  [Versioned PDF](https://arxiv.org/pdf/2411.09347v1)

[defs]: ../../Silmaril/SSA/RVSDG/Categorical/Defs.lean
[thms]: ../../Silmaril/SSA/RVSDG/Categorical/Thms.lean
[base]: rvsdg.md
[lambdassa]: ../../Silmaril/SSA/Isotope/LambdaSSA/Categorical/Defs.lean
[freyd]: ../../Silmaril/Semantics/Categories/Thms.lean
[institutions]: ssa.md
