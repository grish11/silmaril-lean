# The deterministic RVSDG θ institution

A sentence is an equation between two typed [whole-region θ graphs](rvsdg-theta.md).
The sides share a carried port signature and have independent numbered
primitive/γ bodies. For every input, satisfaction compares all returned
tuples and whether each graph admits infinitely many completed continuing
iterations. Iteration counts and internal body observations are outside the
equation's observation. [Definitions](../../Silmaril/SSA/RVSDG/Theta/Institution/Defs.lean)

Signatures, indexed opcode maps, total deterministic models and their
reducts come from the [acyclic RVSDG dialect institution](rvsdg-institution.md).
The sentence map relabels the two bodies, retaining their ordered ports and
feedback. One body step agrees after relabelling and reduction, including
both the continue tag and the updated tuple. Consequently the same finite
return derivations and infinite restart sequences witness the two loop
observations. These equivalences give the satisfaction condition in the
repository's `Sign ⥤ Room` interface. [Theorems](../../Silmaril/SSA/RVSDG/Theta/Institution/Thms.lean)

The checked example migrates two indexed body opcodes to a single target
opcode. The translated equation and its reduct hold, and on input zero the
translated loop returns three after three body executions. In a source
model where one opcode stops and the other continues indefinitely, the
source equation fails. [Fixture](../../tests/ssa/RVSDGThetaInstitution.lean)

The institution concerns one enclosing tail-controlled θ per side, with
acyclic bodies and discrete model categories. Equality in the categorical
interpretation using Elgot iteration is a separate comparison. Nested θ,
arbitrary infinite Petri schedules, and explicit runtime-wire effects
require further syntax or observations.

## Reproduce

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Theta.Institution.Thms
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.Theta.Institution.Thms
lake env leanchecker Silmaril.SSA.RVSDG.Theta.Institution.Thms
```

## Sources

- Nico Reissmann, Jan Christian Meyer, Helge Bahmann and Magnus Själander,
  *RVSDG: An Intermediate Representation for Optimizing Compilers* (2020),
  arXiv:1912.05036v2, §4.1.3 Definition 3. PDF SHA-256
  `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
  [Versioned PDF](https://arxiv.org/pdf/1912.05036v2)
- Joseph A. Goguen and Rod M. Burstall, *Institutions: Abstract Model Theory
  for Specification and Programming* (1992), §2.1 Definition 1 and §2.5
  Definition 12. PDF SHA-256
  `f6715ca333dd03dc153a65907c1c974fa151690bb94eafffc065c363265b634d`.
  [PDF](https://courses.grainger.illinois.edu/cs522/sp2016/InstitutionsAbstractModelTheory.pdf) · [DOI](https://doi.org/10.1145/147508.147524)
