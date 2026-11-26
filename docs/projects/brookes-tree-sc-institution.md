# TreeSC in the concrete Brookes institution

Import `Silmaril.Logic.BrookesSC.TreeSC.Thms` to use the comparison between
[TreeSC's completed behavior][tree] and the [concrete C2 institution][c2].

## World and encoding

For a type of cell names `R` with decidable equality, `TreeSC.world R` has
one thread, values of type `Nat` at every cell, and empty mutex and external
sort types. The cell type itself can be infinite. `storeEquiv R` pairs a
TreeSC memory `R → Nat` with the unique empty mutex-owner map. The inverse
projects memory, and the two inverse laws cover every concrete store in
this world.

The source signature `TreeSC.signature R` provides one label in each
designation fiber. An arrow `labels` out of it chooses labels of the same
designations in a target signature over this world. `encode labels` uses
the actual C2 primitive calls. A load preserves its plain or SC-atomic
designation and passes the Nat reply to the original continuation.
A write preserves its mode, cell and payload and identifies the unique
C2 `PUnit` reply with TreeSC's `Unit` reply. Both modes give the same
primitive store effect. The terminal result of a code program is `Unit`.

## Comparison and satisfaction

- `Trace.mapStores` maps both endpoints in each transition. `Reduces.mapStores`
  carries every stuttering and mumbling deduction. For a store equivalence,
  `Behavior.transport_accepts_iff` recovers the original word by applying the
  inverse. Transport preserves return, bind and singleton completion.
- `eval_encode` identifies C2 model evaluation of the encoded program with
  the transported completed behavior of its TreeSC weak ITree. Its primitive
  cases use C2's `primitive_accepts_iff` and its program cases use
  `eval_ret` and `eval_call_primitive`. Equality covers entire saturated
  words, including open joins that can change the store between operations.
- `satisfies_iff` identifies satisfaction of `inequation labels lhs rhs`
  with inclusion of completed tree words at each valuation. Each side of
  the inequation is a family of `Code R` programs indexed by the same input
  type. The inverse store map reflects inclusion. `encode_translate` and
  `inequation_translate` commute with further designation-preserving label
  maps by composing the chosen labels. `eval_encode_reduct` identifies
  evaluation after that translation with evaluation in the reduct.
  `satisfies_reduct` gives the corresponding satisfaction law.
- `eval_encode_completes_iff_sc` restricts the full-word equality to singleton
  words and recovers contiguous completion in the Track A scheduler with one
  thread. The theorem existentially hides the scheduler event word.

This is a comparison for the well-founded read/write code inside TreeSC.
Each accepted word comes from a finite completed observation. A load can
select code using an arbitrary Nat reply. Internal choices in a general
TreeSC coalgebra are governed by C3's union laws. Here an alternative
represented by `Code` can be encoded individually. Mutex operations,
external requests, interleaving of multiple threads, race observations and
changes of world are outside the fragment.

The [regression][regression] maps the original labels to `true` in a
Boolean-labeled signature. The translated increment reads with the
SC-atomic tag and writes with the plain tag. It accepts a gapped word that
reads 1, resumes at the environment's 0 and writes 2. The open inequation
against setting the cell to the input amount fails at amount 1. The
increment can run contiguously from 1 to 2, and setting the cell to 1
cannot produce that singleton.

## Reproduce the checks

```sh
targets='+Silmaril.Logic.BrookesSC.TreeSC.Thms +Silmaril.Proofs.Logic.BrookesSC.TreeSC.Regression'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
lake env lean -DautoImplicit=false -DwarningAsError=true tests/logic/brookes-sc/TreeSCAxioms.lean

for mod in Silmaril.Semantics.Brookes.StoreEquiv.Defs \
  Silmaril.Proofs.Semantics.Brookes.StoreEquiv \
  Silmaril.Semantics.Brookes.StoreEquiv.Thms \
  Silmaril.Logic.BrookesSC.TreeSC.Defs \
  Silmaril.Proofs.Logic.BrookesSC.TreeSC.Comparison \
  Silmaril.Logic.BrookesSC.TreeSC.Thms \
  Silmaril.Proofs.Logic.BrookesSC.TreeSC.Regression
do
  SILMARIL_REPLAY_MODULE="$mod" lake env lean -DwarningAsError=true tools/compiler-explorer/Replay.lean || exit
done
```

## Primary sources

- S. Brookes, *Full Abstraction for a Shared-Variable Parallel Language*,
  1996, especially §6 on initial/final-store observations. [Paper][brookes]
- Y. Dvir, O. Kammar, O. Lahav and G. D. Plotkin, *Two-sorted algebraic
  decompositions of Brookes's shared-state denotational semantics*, 2025,
  for the return-bearing formulation. [Paper][dklp]
- J. A. Goguen and R. M. Burstall, *Institutions: Abstract Model Theory
  for Specification and Programming*, 1992, for satisfaction under
  translation and reduct. [Paper][institution]

[tree]: brookes-tree-sc-closed.md
[c2]: brookes-sc-concrete.md
[regression]: ../../Silmaril/Proofs/Logic/BrookesSC/TreeSC/Regression.lean
[brookes]: https://doi.org/10.1006/inco.1996.0056
[dklp]: https://arxiv.org/abs/2501.15104v3
[institution]: https://doi.org/10.1145/147508.147524
