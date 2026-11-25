# Coloured firing for compositional θ

This slice covers the simple operations and γ/θ region interfaces of
Reissmann, Meyer, Bahmann and Själander, *RVSDG: An Intermediate
Representation for Optimizing Compilers*, arXiv:1912.05036v2, §§4.1–4.3.
The versioned PDF has SHA-256
`861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
[Paper](https://arxiv.org/abs/1912.05036v2) · [PDF](https://arxiv.org/pdf/1912.05036v2)

Each active region has typed argument and output places. Reads retain
their colours, so an origin can feed multiple users. A vertex is
pending, waiting with one live child, or done with published outputs.
Primitive firings publish directly. Entering γ creates only the selected
arm's marking. Entering θ creates its body marking with the carried
tuple. A child fires through its parent's waiting token with a fresh
local prefix. When the θ child completes and requests feedback, restart
discards its marking and starts a fresh activation with the updated
tuple. A stopped θ or completed γ publishes the outputs and disposes of
its child. An independent later vertex can fire while a child is active.
[Definitions](../../Silmaril/SSA/RVSDG/NestedTheta/Petri/Defs.lean)

`finishes_toTerm` proves existence and correctness of finite completed
firing sequences against `Term.Returns`, the independent unbounded finite
execution relation. The observation is the full ordered result tuple,
including state ports. Soundness interprets the work remaining in a
marking as a relation and proves each individual firing preserves it.
At restart, a completed body supplies exactly the feedback tuple from
which the remaining relational execution proceeds. Completeness composes
explicit entry, inner firing, restart and commit steps by induction on
term execution and finite θ iterations. These proofs include interleaved
legal traces. `finishes_iff` also relates the observations to
`Graph.Returns` using the existing evaluator adequacy theorem.
[Theorems](../../Silmaril/SSA/RVSDG/NestedTheta/Petri/Thms.lean)

The fixture exhibits an eight-step trace with θ inside a selected γ arm
and an unrelated root firing between the two child iterations. It
checks the fresh pending marking and the returned value/state tuple.
All proofs concern finite completion. Progress from every partial marking,
termination of every maximal run and divergence classification remain open.
[Fixture](../../tests/ssa/RVSDGNestedPetri.lean)

```sh
lake build --wfail +Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGNestedPetri.lean
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.Petri.Thms +Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms'
```
