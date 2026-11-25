# The Cartesian RVSDG equation institution

`categoricalInst` interprets the [typed RVSDG dialect equations](rvsdg-institution.md)
in a fixed Cartesian monoidal category. Its signatures and sentences are
shared with the deterministic institution. Its discrete models choose objects
for value and snapshot sorts, finite selector cocones for γ, and arrows for
primitives. Satisfaction compares arrows at the common ordered graph
boundary. The result can include both state snapshots and selector ports.
[Definitions](../../Silmaril/SSA/RVSDG/Institution/Categorical/Defs.lean)

A signature morphism relabels each primitive at the same indexed input and
output signature, including primitives inside γ arms. The model reduct keeps
all port objects and the chosen selector cocones. It interprets each source
primitive by the arrow of its target image. `mapTerm_denoteOpen` proves the
relabelled term and the original term in the reduct give the same arrow
at every open prefix. The γ case equates the arm families pointwise before
applying the same coproduct eliminator. The term–graph agreement theorem
transfers this to numbered graphs. Applying the result to both sides of
an equation proves the corridor's satisfaction condition. [Theorems](../../Silmaril/SSA/RVSDG/Institution/Categorical/Thms.lean)

`toRuntime` is an institution comorphism from the Cartesian institution in
`Type` to the deterministic institution. Its signature functor and sentence
components are identities. Its contravariant model component sends a runtime
model to `Categorical.Model.ofRuntime`, using the tuple encoding and the
standard finite selectors. This adapter commutes with every dialect reduct
on model objects. The deterministic characterization of graph arrow equality
proves the comparison's satisfaction equivalence. The three-arm opcode
migration fixture checks the categorical corridor and both a satisfied and
a refuted equation under the comparison. [Checked fixture](../../tests/ssa/RVSDGInstitution.lean)

The category is fixed throughout reindexing, and its chosen products give
every port the structural maps of a value, including state snapshots. The
sentence syntax covers acyclic primitive and multiway γ graphs. A λSSA
equation-level comparison, θ, and ordered effects require extensions.

## Reproduce

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Institution.Categorical.Thms
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.Institution.Categorical.Thms
lake env leanchecker Silmaril.SSA.RVSDG.Institution.Categorical.Thms
```

## Sources

- Nico Reissmann, Jan Christian Meyer, Helge Bahmann and Magnus Själander,
  *RVSDG: An Intermediate Representation for Optimizing Compilers* (2020),
  arXiv:1912.05036v2, §4.1.2. PDF SHA-256
  `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
  [Versioned PDF](https://arxiv.org/pdf/1912.05036v2)
- Joseph A. Goguen and Rod M. Burstall, *Institutions: Abstract Model Theory
  for Specification and Programming* (1992), §2.5 Definition 12. PDF SHA-256
  `f6715ca333dd03dc153a65907c1c974fa151690bb94eafffc065c363265b634d`.
  [PDF](https://courses.grainger.illinois.edu/cs522/sp2016/InstitutionsAbstractModelTheory.pdf)
- Joseph Goguen and Grigore Roşu, *Institution Morphisms* (2002), §4
  Definition 4.2. PostScript SHA-256
  `6c6d04dac67a1db23be799fb6afac4a488bdc74e69dd6cbfa4f3e66d1cf717ed`.
  [PostScript](https://cseweb.ucsd.edu/~goguen/pps/rodfest.ps) · [DOI](https://doi.org/10.1007/s001650200013)
