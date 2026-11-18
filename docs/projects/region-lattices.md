# Abstract region models form complete lattices

The abstract core depends only on typed judgment carriers and fixed positive
inference rules. Execution, memory, graphs, decidability, finite enumeration,
and operations on supports/exits are absent. Semantic models and binary/CFG
adapters are separate interpretations. The [region extraction guide](region-extraction.md)
describes those layers and their remaining gates. The
[tree/CFG layer](region-trees.md) instantiates the same lattices at tree and CFG
judgment carriers, without requiring a graph for primitive tree regions.

## Public API and specialization

| Header | Purpose |
| --- | --- |
| [`Abstract/Defs`](../../Silmaril/Semantics/Region/Abstract/Defs.lean), [`Thms`](../../Silmaril/Semantics/Region/Abstract/Thms.lean) | Arbitrary signatures, raw models, fixed positive rules, closure, complete lattices, ceilings and transport |
| [`Abstract/Named/Defs`](../../Silmaril/Semantics/Region/Abstract/Named/Defs.lean), [`Thms`](../../Silmaril/Semantics/Region/Abstract/Named/Thms.lean) | The five segment predicates and label-only predicate; raw and lawful lattices |
| [`Abstract/Examples/Thms`](../../Silmaril/Semantics/Region/Abstract/Examples/Thms.lean) | Union versus join, existential forgetting versus meet, nonemptiness versus meet |
| [`Lattice/Thms`](../../Silmaril/Semantics/Region/Lattice/Thms.lean) | Compatibility with the existing finite-set profile and its lawful record |

All names below are in `Silmaril.Semantics.Region.Abstract`, unless stated
otherwise. `Signature` has an arbitrary type `Shape` and an indexed argument
family `Args : Shape → Type`. Its atom type is `Sigma Args`; `Signature.Model`
is the powerset of those atoms. A client can also supply an atom type directly.
There is no requirement to use the named vocabulary.

The named segment model has six independent carrier parameters:

```lean
SegmentRegionModel Img Assum Seg Support Lab Exits
```

Its fields are the raw predicates `SegBB`, `BB`, `SR`, `SR'`, and `Reg`.
`Support` and `Exits` need not be sets or collections. The label-only model is
`RegionModel Img Assum Lab Exits`. `SegmentAtom` is the typed disjoint union of
the five judgment shapes; `LabelAtom` holds the four label-judgment arguments.
The `toAtoms`/`ofAtoms` equivalences have proved inverse equations and order
isomorphisms. Thus neither encoding loses judgments or identifies predicates.

The previous `Silmaril.Semantics.Region` API is now an alias of this named
API at `Support := Finset Seg` and `Exits := Finset Lab`. Its row serializers,
helpers and semantic theorems retain their interfaces. Its original lawful
record is equivalent to a positive-rule closed model and inherits a complete
lattice. There is one predicate and coherence implementation, rather than
parallel copies with different obligations.

## Raw models and positive laws

`RawModel Atom` is `Set Atom`. Inclusion is pointwise implication. Raw meets
are intersections, joins are unions, bottom is empty, and top contains all
typed atoms. These operations allow arbitrary families, including empty ones.

A `Rule Atom` consists of `premises : Set Atom` and `head : Atom`. A fixed set
`rules : Rules Atom` selects the permitted rules. Premises can be infinite;
empty premises express unconditional facts. A model is `Closed rules M` when
every rule whose premises belong to M has its head in M. Compatibility,
entry/interface/frame requirements, support/label constraints, and wiring
conditions must select rules independently of M. They can be arbitrary
propositions on the participating atoms and external fixed parameters. They
cannot test absence of a judgment or choose applicability according to which
incompatible existential witness M happens to contain.

`glueRules compatible` is an optional two-premise schema with such a fixed
compatibility predicate. It supplies no execution theorem: an interpretation
must separately prove every selected rule sound for that interpretation.
The first-exit gluing theorems use actual crossing states and entry invariants;
they are not replaced by a syntactic rule about subtracting exit labels.

`BoundaryOps` optionally supplies singleton support, singleton exit and
option-to-exit functions. `CoherenceRules ops` encodes BB → SegBB and BB → Reg,
SR ↔ singleton-exit Reg, and SR' ↔ optional-exit Reg as six unary positive
rules. `coherence_iff` proves equivalence with the field-style
`SegmentRegionLaws ops`. No property of those functions is assumed. Meaning
such as "singleton" belongs to the chosen profile/interpretation. The finite
profile supplies the actual finite-set operations.

## Lawful complete lattices

`closure rules M` is the intersection of every closed model containing M.
The full atom set is closed, so an extension always exists. Theorems establish
extensiveness, monotonicity, idempotence, closedness and the least-extension
property. `closed_sInf` proves arbitrary intersections are closed directly.
A `ClosureOperator` and its Galois insertion then construct the formal
`CompleteLattice (ClosedModel rules)` instance.

The same construction transfers to both named lawful model types:

```lean
LawfulSegmentRegionModel (rules : Rules (SegmentAtom ...))
LawfulRegionModel (rules : Rules (LabelAtom ...))
```

The order is still implication/inclusion of the underlying judgments; it is
not an order on helper functions or on proof objects. `val_sInf`, `val_sSup`,
`val_bot`, `val_top` and the `lawful_segment_*`/`lawful_label_*` theorems expose
the operations:

| Operation | Underlying set of judgments |
| --- | --- |
| Arbitrary meet | Intersection of all the models |
| Arbitrary join | Closure of the union of all the models |
| Bottom | Closure of empty |
| Top | All typed atoms |
| Binary meet | Set intersection |
| Binary join | Closure of set union |

Bottom need not be empty when rules contain facts. Top is an abstract lawful
model; it makes no semantic soundness claim.

The checked example uses a label-only signature and one rule `{0,1} ⇒ 2`.
`left = {0}` and `right = {1}` each satisfy the rule because a premise is
missing. Their union omits 2 and is not closed (`union_not_closed`). Their
lawful join contains 2 (`composed_in_join`). Hence replacing lawful joins by
union would violate the requested laws even for a finite two-premise schema.

## Fixed ceilings and separate strata

For a **lawful** fixed ceiling C, `Below C := Set.Iic C` has a complete lattice.
`closure_below` proves closure of any subset of C stays below C. `below_sSup`,
`below_sInf`, `below_bot` and `below_top` expose its operations:

- Joins are the inherited closed joins, hence closure of the raw union.
- Meets are C intersected with the inherited meet. For nonempty families the
  C bound is redundant; for an empty family it is essential.
- Bottom is closure of empty; top is C.

To use semantic soundness as a ceiling, fix the semantics, observations,
entry-domain policy and row interpretation first. Prove the chosen rules
preserve that ceiling before constructing its `ClosedModel` certificate.
The abstract lattice does not assume this certificate or assert that the
particular finite semantic `Valid` relation already satisfies arbitrary rules.
Without rules, all sets of rows below any fixed admissibility predicate are
simply a powerset interval and already form a complete lattice.

This distinction matters for stronger specifications:

- A fixed per-row soundness, well-formedness, nonvacuity or exactness predicate
  can define an admissibility ceiling. Combining it with rules needs a proof
  that the ceiling is closed. Exactness may invalidate rules that enlarge exit
  allowances; domain restrictions may invalidate reachable-exit exactness.
- Requiring the **model** to contain some judgment is different. The example
  `nonempty_not_meet` gives two nonempty closed models with empty intersection.
  Such a subtype does not inherit the claimed intersection lattice.
- Requiring a model to provide some boundary witness for every SegBB also
  needs care: independent models may provide different witnesses. The core
  instead uses only the positive BB → SegBB rule; SegBB carries no boundary.
- Helper lookup/extraction functions decorate a model with additional data
  and soundness obligations. Partial lookup means unknown, not empty. No
  complete lattice on these decorated records is asserted.
- Model-dependent negative premises, unique/maximal partitions and algorithms
  choosing representative regions are not positive inference laws. They live
  in separate specifications. The greatest set of semantically sound rows
  does not choose a unique maximal partition.

## Erasure and reindexing limits

`forget f M` is direct image, so it existentially forgets atom information.
`forget_sSup` proves preservation of all raw joins. `forget_not_meet` supplies
a counterexample to meet preservation: two different source atoms both map
to Unit, and their singleton models have empty intersection while their
images intersect. This is the same witness issue as existential support
erasure. No general lawful-join or lawful-meet preservation is claimed for
such erasure.

`reindex f M` is inverse image. `reindex_sInf` and `reindex_sSup` prove raw
preservation of both arbitrary operations. `RuleMap` requires each source
rule to have a target rule with the mapped head and premises contained in
the image of the source premises. This fixed condition proves
`reindex_closed`; combined with `reindex_sInf_closed` it transports closed
intersections. `closure_reindex_le` proves the useful one-sided bound:

```
closure source (reindex f M) ⊆ reindex f (closure target M)
```

Equality, and therefore lawful-join preservation, requires additional
hypotheses. The finite-profile institution's satisfaction condition remains
separate; these lattice results do not claim arbitrary gluing is categorical.

## Verification

Run the pinned toolchain without adding dependencies:

```sh
lake build --wfail Silmaril.Semantics.Region.Abstract.Examples.Thms \
  Silmaril.Semantics.Region.Examples.Thms
```

The second root exercises the finite-profile compatibility layer. The PR's
verification report records the full set of adapter targets and the scoped
`make check` invocation. These are kernel proofs, including the examples;
there is no finite model enumeration or external solver hidden in the lattice
construction. No `sorry`, new axiom or `native_decide` is used.
