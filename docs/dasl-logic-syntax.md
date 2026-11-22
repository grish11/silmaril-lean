# DASL presentations for logic syntax

This is an abstract DASL profile over decoded values and finite object expansion.
It reuses the repository's `SE` presentations, `ValueNames` resolution,
`TotalCodec` recovery contract, and `Consequence.System` interface. It neither
defines a wire format nor assigns CIDs. A store must justify its own object names.

## Common profile

Atoms are DASL strings and an S-expression list is a DASL list with the same
slots. A nullary production can be a string. Canonical decimal atoms are used
for unbounded indices and universe levels; their range is not restricted to
I64. Tags, index atoms, and symbol labels remain inline. The rendering table
specifies how many slots, starting at zero, are inline metadata:

| Grammar | Inline prefix of a list |
| --- | --- |
| HOL Light | 2 for `tyvar`, `tyapp`, `bvar`, `fvar`, `const`; otherwise 1 |
| Extensional MLTT terms/types | 2 for `fv`, `bv`, `univ`; otherwise 1 |
| Extensional MLTT context | 1 for the context and each declaration; term rules below a declaration |
| One-sorted FOL | 2 for `var`, `app`, `rel`; otherwise 1 |
| PA | 2 for `var`; otherwise 1 |

The `ctx` list in HOL has variable zero first; MLTT declarations are oldest
first and can depend on earlier declarations. A HOL `hyps` list presents
assumptions, not bound-variable types. Its entailment interpretation takes
`toFinset`, discarding order and repetitions. The independent ordered-set
representation uses the reusable `Encode.setOf` layout, with a caller-supplied
recoverable term-to-key codec and key-to-DASL codec. The list/set compatibility
theorems apply to any binding hypothesis-name resolver, as well as the DASL
layout. They require the contexts to resolve to the same hypothesis set and
are not equivalences for typing contexts.

In the optional policy every child slot can be separately inline or an object
edge, selected by an index path. In `linkAll` every such slot, even a nullary
child, is an object edge. The outer root is unwrapped in either policy and
can itself be stored under a name. For example the PA spelling `(= (+ zero
zero) zero)` is fully inline as `["=", ["+", "zero", "zero"], "zero"]`.
Fully linked it can be `["=", obj(add), obj(zero)]`, where `add` is
`["+", obj(zero), obj(zero)]` and `zero` is the string `"zero"`.

`Syntax.recover_write` proves recovery for every placement. `linkAll_optional`
includes the maximal policy in the optional family, and
`normalize_of_optional` recovers the same maximal expanded form regardless of
the accepted input placement. This does not synthesize names or require the
store to contain another placement of the object. `recover` is intentionally
permissive about where it opens already expanded `obj` wrappers. `presents`
and `optional`, not success of `recover` alone, assert policy conformance.

## Names and judgments

`Naming.Lift` accepts heterogeneous tuples. Each coordinate independently
relates a surface value to a meaning: direct equality, a supplied encoding,
or a name relation composed with an encoding. `ValueDecoders` specializes
this to all-DASL inputs. `namesWhere` is the unary name language. Its membership
theorem factors recognition through an abstract DASL language, of the same
existential shape as `Dasl.Recognized`; it does not require the separate
language/checker stack. `system` lifts existing binary consequence systems;
`system_of_match` recovers an underlying judgment once both coordinates bind
and resolve. Multiple names may alias one value. Only binding (one meaning per
name under the stated hypotheses) is used for soundness.

- **HOL Light:** Syntax includes raw terms/types, including explicitly
  instantiated constants. Scope, type-operator arities, constant arities and
  proposition type are checked by the existing signature-relative typing
  judgment, not by parsing. `propositions`, `theorems`, and `validIn` mean,
  respectively, Boolean typing, kernel derivability with a supplied theory,
  and truth at all valuations of a supplied model. Derivability implies
  semantic entailment when the model satisfies the theory.
- **Extensional MLTT:** Types and terms share `ETm` syntax; binding depth and
  universe levels use the existing parser. `types` uses universe formation,
  `typing` checks a given represented term, and `inhabitance` quantifies over
  a term in a well-formed context, including terms not present in the store.
  `semanticInhabitance` instead asks for a member of the denoted set at every
  satisfying environment of a supplied hierarchy. Soundness is one-way; no
  hierarchy is constructed here, and there is no decision or completeness
  claim. The mixed length operations agree for exactly `0 ≤ n < 2^63`, and
  `natI64_exact` proves that the accepted bits have signed value `n`.
- **FOL/PA:** The arbitrary-signature profile uses the repository's one-sorted
  FOL syntax and requires an explicit arity-preserving label isomorphism.
  The parser checks the label namespace, arity, and bound indices. Logical
  validity means truth in every model, distinct from the derivation-tree
  predicate. The separate built-in arithmetic grammar uses the PA proof
  system and standard-natural-number truth, not all-model truth. In both
  cases the name-level implication is soundness, not completeness.

## Reproduce

```sh
lake build --wfail +Silmaril.ProofFormats.DaslSyntax.HOL.Thms \
  +Silmaril.ProofFormats.DaslSyntax.FOL.Thms +Silmaril.ProofFormats.DaslSyntax.PA.Thms \
  +Silmaril.ProofFormats.DaslSyntax.MLTT.Thms +Silmaril.ProofFormats.DaslSyntax.MLTT.Semantics.Thms \
  +Mathlib.Tactic.FinCases
lake env lean -DwarningAsError=true tests/formats/DaslLogic.lean
```

The fixture supplies shallow lookups and finite expansion derivations for a PA
theorem, a valid FOL sentence, a HOL typing judgment, and MLTT context length.
It checks both fixed-type MLTT term-name membership and named inhabitation with
no root for the witness. It also checks malformed inputs, the signed boundary,
and prints transitive axioms.
The many-sorted FOL institution needs a separate codec carrying sort and
argument-sort labels. Prolly closed scans should be connected through
`Lift.codedSet` and `HOL.derivesWith`/`HOL.entailsWith`, without treating an
unresolved or invalid block as an empty set.
