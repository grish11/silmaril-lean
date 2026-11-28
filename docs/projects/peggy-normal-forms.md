# Stable normal forms for Peggy saturation

Section 4 of Tate, Stepp, Tatlock and Lerner, arXiv:1012.1802v3,
printed pp. 20–21, orders abstract IRs by inclusion of their nodes and
equalities. Equation (4.1) makes each labelled analysis step inflationary.
Equation (4.2) simulates a labelled step into a larger IR by one step of the
same analysis whose result covers the original successor. An analysis may
choose to leave the IR unchanged. Equation (4.3) follows by taking the
intervening successor as the larger IR. [Paper](https://arxiv.org/pdf/1012.1802v3)

For (4.4), the paper filters the union of analysis steps by literal
inequality of source and target. A normal form is reachable by a finite
trace of those filtered steps and has no outgoing filtered step. The
printed uniqueness claim uses the stated **partial order**, including
antisymmetry, and monotonicity of every analysis in the selected family.
Uniqueness compares two such forms. The paper's separate convergence
discussion assumes termination on all inputs.

## Proof and preorder interpretation

The [generic interface](../../Silmaril/SSA/Peggy/EPEG/Saturation/NormalForms/Thms.lean)
uses a labelled transition family, an explicit preorder relation, and
separate inflationarity and simulation hypotheses for each analysis.
`delayed_step` formalizes (4.3) and is used by the E-PEG comparison API.

`Stable` means that every labelled successor is covered by the current
state. By inflationarity this is exactly the condition that all steps
from it are order-equivalent stutters. `StableNormalForm` also requires
finite reachability by the union of labelled steps, where stutters are
allowed. `stable_iff_no_progress` expresses stability as absence of an
outgoing strictly growing step.

To bound a finite trace by a stable state, start with any comparison
from its source to the bound. Simulate each next labelled step at that
bound. The resulting successor covers the next trace state and is
itself covered by the bound, so transitivity preserves the comparison.

- `stableNormalForm_least` proves that a reachable stable state is a
  least stable upper bound of the source, including among stable bounds
  outside the reachable set. It also covers all reachable states by the
  same bounding lemma.
- `stableNormalForm_unique` compares any two reachable stable states in
  both directions. `Extension.stableNormalForm_unique` instantiates this
  result with the typed E-PEG embedding preorder from the
  [node-monotonicity development](peggy-node-monotonicity.md).
- `paperNormalForm_unique` proves literal equality with the paper's
  definition. Deleting literal self-loops preserves reachability.
  Antisymmetry and inflationarity then make stability equivalent to the
  absence of a nonidentity step. Raw numbered E-PEG states can compare in
  both directions while using different addresses or class labels, so
  the embedding result uses mutual comparison.

## Regressions and growth

The regression runs a finite family of two mark-setting analyses. From
the empty state, either mark can be added first. Both two-step traces
reach the full state, where a stuttering analysis is still enabled.
The proof establishes literal uniqueness for this partial order.

A separate regression gives a three-state preorder with two distinct
terminal representatives above a seed. The analysis is inflationary and
monotone, and both representatives satisfy the paper's identity-filtered
normal-form predicate. Their distinct identities show that extending the
literal equality conclusion to preorders would be false. The repaired
conclusion proves mutual comparison. The stated partial-order theorem
needs no stronger progress or termination hypothesis.

For the fresh-append zero-sample family, `ZeroSample.progress` rules
out a reverse embedding after a step by cardinality. The match
survives appending, so `ZeroSample.grows` constructs finite traces with
arbitrarily many new rows. `ZeroSample.no_stable` proves that every
state reachable from a matched seed still has a strict step. The cyclic
regression exercises this even with an equivalent RHS already present.
The proof concerns this append policy. The normal-form theorem remains
conditional on reachability and stability, with no termination or
arbitrary node reuse result.

```sh
lake build --wfail +Silmaril.SSA.Peggy.EPEG.Saturation.NormalForms.Thms +Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Comparison.Thms PeggyEggTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PeggyEgg.lean
lake env leanchecker --fresh Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Comparison.Thms
lake env leanchecker tests.ssa.PeggyEgg
```
