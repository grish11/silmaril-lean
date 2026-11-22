# Pattern-indexed DASL types and systems

`Silmaril.Calculi.PERConstraints.Patterns.Dasl.Thms` instantiates the typed
pattern institution on DASL trees. It uses `PER.Constructors` and the
`PERConstraints.Congruence` signature, constructor maps, and full-closure model
without defining another constructor or PER calculus.

## Three levels of semantics

- A **pre-semantic type** is a plain `PER` on syntax. Self-related terms are its
  valid terms; there is no ambient reflexivity requirement.
- A **full semantic type** is a `Congruence.Model`: the PER is closed under
  every enabled constructor, using that same relation for all children and the
  result.
- A **selected-pattern semantic type** is one family component at an output
  index, satisfying `SemanticAt` relative to the family interpreting its hole
  types. A **system** selects a set of rules and requires them all; unrelated
  constructors or type assignments impose no additional closure.

All indices share the DASL tree carrier. Each rule declares a finite arity, a
type index for each `Fin` hole, a result index, and a constructor tree with
holes. Repeated occurrences of an index use the *same* substitution and the
same premise. Every declared index supplies a premise even if unused; in
particular, an unused hole at an empty PER can make a rule vacuous. Constructor
nodes branch over the actual DASL child positions (dictionary keys, list
positions, object children, or no children). The generic pattern definition
works over other guarded signatures too, without asserting finite branching
there.

`Rule.Holds` tests every pair of substitutions. All hole pairs must be related
in their declared PERs, and both plugs must pass every guard at constructor
nodes of the pattern. No guard is checked *inside* a substituted hole term.
The plugs must then be related in the result PER. At arity zero the hole
premises are vacuous: an enabled ground pattern must be valid at the result.

`System.uniform` copies one fully congruent PER into every index. It satisfies
every system, commutes on underlying families with the existing full-model
reduct, and the copy is injective when an index exists. For heterogeneous
families, a sufficient condition for each rule is full closure of its output
PER and inclusion of every hole PER in that output PER. Full closure of every
component individually is **not** sufficient. `System.closure` is the least
extension of a seed family satisfying the selected rules, by pointwise
intersection of all simultaneously extending families. It is a semantic
construction, not an executable saturation procedure.

## Category and institution

The institution has rule sentences and discrete models of pre-semantic PER
families. A signature map combines a constructor-commuting syntax translation
with an index map. Sentence translation maps constructor shapes and type
indices; reduct reindexes the family and pulls each component back along the
term map. `satisfaction` proves an equivalence, not only a preservation
implication. For this universal rule language a signature map must lift all
target terms, cover every source child position, and reflect as well as preserve
guards on the translated tuple. These conditions let the proof lift target
substitutions and recover both source guards; mere forward guard preservation
does not justify that direction. Neither term nor index maps must be
injective. For DASL the positions are unchanged and surjective reference and
name maps give surjective tree maps.

Systems reuse the repository's `Presentation` category on this institution.
A morphism sends each selected source rule to a selected target rule; the
model reduct therefore preserves system satisfaction. A `System.Model` is a
family satisfying the presentation, unlike the unrestricted families in the
underlying institution.

## Checked example and limits

`Patterns.Dasl.Examples.Thms` checks a two-element list pattern with two narrow
holes. Widening just the first hole makes the rule fail on `[true, null]`, with
the same pattern, result type and guards. The narrow system accepts the
example family, and its least closure leaves that family unchanged even
though the result PER is not closed under enabled unary lists. Another family
has full closure at each index but fails the narrow rule. A repeated-hole
example checks plugging and satisfaction under a DASL translation collapsing
references and type indices.

Follow-ons include separate syntax carriers per sort, semantic rather than
syntactic rule maps, and a ground-instance institution for non-surjective
syntax maps. No link resolution, named certificates, union-find, or decision
procedure is provided.

```sh
lake build --wfail Silmaril.Calculi.PERConstraints.Patterns.Dasl.Examples.Thms
make check CHECK_TARGETS='Silmaril.Calculi.PERConstraints.Patterns.Dasl.Examples.Thms'
```
