# Tail-controlled θ in the RVSDG

This slice adds one whole-region θ vertex whose body is an arbitrary
primitive/γ region, including nested γ. Reissmann, Meyer, Bahmann and Själander
give the θ interface in *RVSDG: An Intermediate Representation for Optimizing
Compilers*, arXiv:1912.05036v2, §4.1.3 and Definition 3. The versioned PDF has
SHA-256 `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
[Paper](https://arxiv.org/abs/1912.05036v2) · [PDF](https://arxiv.org/pdf/1912.05036v2)

## Body interface and observations

[Theta.Defs](../../Silmaril/SSA/RVSDG/Theta/Defs.lean) gives the structural
vertex identical input, output and body argument signatures. The body returns
`.control 2 :: carried`. Port zero requests either exit (zero) or repeat (one).
The remaining results become the enclosing outputs on exit or re-enter the
body as its arguments on repeat. The body runs at least once.

`Theta.Term` uses the existing inductive term for its body. `Theta.Graph`
stores the corresponding hierarchical port graph. Their translations
leave the loop interface fixed and translate the body. `Theta.Iterate`
specifies finite return by one final stopping body execution and zero or
more continuing ones. `Theta.Repeats` describes an infinite sequence of
completed continuing iterations. Lean proves the two representation round
trips, term/graph finite return equivalence, and exclusion of divergence
when a graph returns. [Operational theorems](../../Silmaril/SSA/RVSDG/Theta/Thms.lean)

[Theta.Petri.Defs](../../Silmaril/SSA/RVSDG/Theta/Petri/Defs.lean) runs the
existing coloured firing semantics inside an active iteration. A completed
body can either return or re-enter based on its predicate. Re-entry
discards the completed body's cells and installs a fresh pending marking
with the updated carried tuple. The finite return theorem relates **all**
finitely completed θ schedules to the numbered semantics and constructs
a finishing schedule for every numbered return. The divergence theorem
relates infinite iterations to infinitely many completed continuing Petri
bodies. Each such body admits a finite segment ending with an actual
restart step. These statements use completed iteration checkpoints.
Classification of arbitrary infinite or maximal firing schedules is open.
[Petri theorems](../../Silmaril/SSA/RVSDG/Theta/Petri/Thms.lean)

For θ as an ordinary vertex, including in γ arms and other θ bodies,
see the [compositional extension](rvsdg-nested-theta.md).

## Checking and extending the fragment

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Theta.Thms +Silmaril.SSA.RVSDG.Theta.Petri.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGTheta.lean
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.Theta.Thms +Silmaril.SSA.RVSDG.Theta.Petri.Thms'
```

The [fixture](../../tests/ssa/RVSDGTheta.lean) threads a state colour through
two dependent body vertices. It checks a three-iteration return, a mandatory
first iteration at the stopping bound, an always-continuing loop, and the
restart rule installing a fresh marking.

The primitive/γ types and model remain the body interface. The compositional
extension reuses the carried signature and the iteration rules here. For an Elgot
model, the returned predicate routes the updated carried tuple into the
exit or feedback summand of a body map. A future interpretation should
prove finite return and divergence adequacy against the corresponding
operational observations.
