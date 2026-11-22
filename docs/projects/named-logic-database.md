# Named HOL and MLTT judgments

`Silmaril.ProofFormats.DaslSyntax.Database.Thms` lifts existing consequence systems
and typing relations. Coordinates may use direct syntax, abstract DASL with a
representation relation, or arbitrary names with an interpretation relation.
Rows assert existence of the recovered inputs and the actual logical judgment.
Binding lets one compare rows at established interpretations; reverse uniqueness
of names is not required. A failed lookup does not refute a judgment.

HOL derivability uses `HOLLight.Derives` with an explicit theory and a finite set
of hypotheses. A set may be resolved by its root or by a list or finite set of
members. The list/finite comparison requires binding, matching name membership
and successful resolution. HOL typing uses `HasType` with an ordered bound
context, distinct from the hypothesis set. Its binary projection fixes a context.
`closedTheorems` additionally requires a locally closed term with no free term
variables; it allows schematic type parameters. Proposition typing, type formation,
and truth in a supplied model are distinct. The entailment inclusion assumes that
the model satisfies the theory.

MLTT uses the extensional `ECtx.JEq` calculus. Formation requires a universe in
a well-formed context; typing checks a supplied term. Inhabitation quantifies
over a term, not its name. The tables neither decide derivability nor assert a
converse to semantic soundness. The examples check a HOL implication under a
named assumption, a closed HOL implication, and the MLTT type
`Σ n : ℕ, Id ℕ n n`, with its pair witness and both projection computations.

```sh
lake build --wfail +Silmaril.ProofFormats.DaslSyntax.Database.Examples.Thms
lake env lean -DwarningAsError=true tests/formats/DaslDatabase.lean
```

This interface does not parse bytes, assign CIDs, or verify hashes. The example
name relations are finite observation tables over opaque identifiers.
