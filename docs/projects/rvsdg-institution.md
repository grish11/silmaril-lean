# The RVSDG dialect institution

The institution uses the numbered primitive and multiway γ graphs of the
[acyclic RVSDG core](rvsdg.md). Its signature category fixes the value and
state sort alphabets. A signature supplies an opcode family indexed by an
ordered input port list and an ordered output port list. A signature morphism
maps each opcode within its indexed family, preserving every port sort,
position, and selector arity. Maps can identify distinct opcodes.

A sentence is an equation between two open graphs with a common ordered
argument and result signature. The two vertex tables have independent
internal signatures. Translation relabels primitives, including those in
nested γ arms, and retains the ports, wires, child regions, and vertex
numbering of both graphs. It uses their exact numbered linearizations.
[Definitions](../../Silmaril/SSA/RVSDG/Institution/Defs.lean)

A model interprets values and state snapshots as types and opcodes as total
deterministic functions. Model categories are discrete. The reduct keeps the
carriers and interprets each source opcode using its target image. A model
satisfies an equation when the two graphs return the same tuple for every
input, including agreement on state snapshots in the result signature.
`mapGraph_run` proves evaluation commutes with reduct. `corridor` uses that
theorem for the satisfaction condition, and `inst` checks the identity and
composition laws in the repository's `Sign ⥤ Room` interface. [Theorems](../../Silmaril/SSA/RVSDG/Institution/Thms.lean)

`Equation.holds_iff_denote` identifies satisfaction with equality of the
categorical graph arrows in the Cartesian category of types. It uses the
independently defined graph arrows of the [categorical milestone](rvsdg-categorical.md)
and the inverse tuple encodings. This characterization uses the same models
and the same returned observations as operational satisfaction.

## Example

A dialect migration identifies a legacy state-advance opcode with its
replacement in a target dialect. An open equation differs in only one of
three γ arms. It holds in the target and its reduct. In a source model where
the two opcodes advance the snapshot by different amounts, selecting the
differing arm refutes the equation. This example exercises equation
translation under γ and the model restriction implicit in satisfaction under
change of signature. [Checked fixture](../../tests/ssa/RVSDGInstitution.lean)

## Scope

The institution concerns fixed sort alphabets, typed acyclic graphs, and
returned tuples under deterministic execution. A λSSA comparison can start
with the admitted unary straight-line equations from the verified translation
and a signature functor that maps typed instructions into the corresponding
RVSDG opcode families. Packaging a comorphism additionally requires
translation of equations on both sides, a functor on matching models, and
naturality under instruction relabelling. The existing λSSA/λRTL institution
has a different syntax and model interface. The comparison, broader
signature maps, θ, divergence, and linear runtime state observations require
separate extensions.

## Reproduce

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Institution.Thms
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.Institution.Thms
lake env leanchecker Silmaril.SSA.RVSDG.Institution.Thms
```

## Sources

- Nico Reissmann, Jan Christian Meyer, Helge Bahmann and Magnus Själander,
  *RVSDG: An Intermediate Representation for Optimizing Compilers* (2020),
  arXiv:1912.05036v2, §§4, 4.1.1–4.1.2 and 4.3. PDF SHA-256
  `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
  [Versioned PDF](https://arxiv.org/pdf/1912.05036v2)
- Joseph A. Goguen and Rod M. Burstall, *Institutions: Abstract Model
  Theory for Specification and Programming* (1992), §2.1 Definition 1 and
  §2.5 Definition 12. PDF SHA-256
  `f6715ca333dd03dc153a65907c1c974fa151690bb94eafffc065c363265b634d`.
  [PDF](https://courses.grainger.illinois.edu/cs522/sp2016/InstitutionsAbstractModelTheory.pdf) · [DOI](https://doi.org/10.1145/147508.147524)
