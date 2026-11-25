# Partial observations of nested explicit RVSDG wires

The bridge covers the existing `ExplicitRuntime.Checked` fragment.
Each entry and result has a final runtime port and data ports typed by
`Data`. The admission witness requires each binding to consume the designated
live token. A γ passes it to the selected arm, and a θ sends the returned
body token to the next activation or the exit. The code keeps the original
numbering and represents the old token slots by unit after erasure.
[Admission and erasure](../../Silmaril/SSA/RVSDG/NestedTheta/ExplicitRuntime/Defs.lean)

The prior checked-wire adequacy theorem covers total `StateM` primitives.
For partial primitives this bridge uses the existing wire model's
`Part`-valued primitive interpretation and its unbounded finite execution
relation. The erased model uses the same pure functions and partial
`StateT σ Part` actions as the [ordered endpoint institution](rvsdg-nested-partial-institution.md).
It reads the store from the actual live origin at an open prefix.

- **Return.** A finite wire derivation corresponds to an erased return with
  the same ordered data and exact final token. The observation equality uses
  the existing numbered wire graph denotation and retains its definedness.
- **Block.** The wire relation detects an undefined primitive at its actual
  operand tuple after successful predecessors. It records the typed opcode,
  data, static path, local vertex and exact token from the failing wire
  input. Erasure changes the opcode to its typed unit-slot form and
  preserves the entire diagnostic.
- **Productive divergence.** Each successful wire restart transports the
  whole carried tuple and token across erasure. This transports finite
  restart prefixes to nested divergent children and infinite sequences of
  completed restarts in both directions.

The result applies to supplied admission witnesses with arbitrary γ/θ
nesting. Undefined primitive actions are atomic blocks. Divergence observes
existence of a productive infinite run. Comparing infinite action traces,
transporting diagnostics under renumbering, and arbitrary premonoidal models
are separate extensions.
[Wire observations](../../Silmaril/SSA/RVSDG/NestedTheta/ExplicitRuntime/Partial/Endpoints/Defs.lean) · [Agreement](../../Silmaril/SSA/RVSDG/NestedTheta/ExplicitRuntime/Partial/Endpoints/Thms.lean)

The fixture assembles a numbered γ whose selected arm has a θ. It checks
feedback from token 2 to 5 to 8. The returning variant produces payload 3
and token 11. The blocked variant attempts payload 2 at token 8 and excludes
divergence. The continuing variant has a productive restart stream. The
bypass arm retains token 2. [Fixture](../../tests/ssa/RVSDGNestedThetaPartialWires.lean)

## Reproduce

```sh
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Endpoints.Thms
lake env leanchecker Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Endpoints.Thms
```

## Source

- Nico Reissmann, Jan Christian Meyer, Helge Bahmann and Magnus Själander,
  *RVSDG: An Intermediate Representation for Optimizing Compilers* (2020),
  arXiv:1912.05036v2, §§4.1.2–4.1.3, Definitions 1–3. PDF SHA-256
  `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
  [Versioned PDF](https://arxiv.org/pdf/1912.05036v2)
