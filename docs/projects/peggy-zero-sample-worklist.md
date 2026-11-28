# Bounded discovery for Peggy zero sampling

The worklist extends the [fixed-site reuse pass](peggy-zero-sample-closure.md)
for the zero-sample analysis in [§5.3 of the Peggy paper](https://arxiv.org/abs/1012.1802v3).
It scans all typed row addresses in the **current** E-PEG. An enabled site
is a structural match of `eval ℓ (θℓ (initial, feedback), zero)` without an
exact `eval ℓ (initial, zero)` row in its class. The RHS comparison includes
the result sort, loop identity and ordered operand addresses. The discovery
pass uses the existing matcher, coverage check, and reuse/append transition.

`run` takes the first enabled address in numeric order and rescans after
each visit. One unit of fuel pays for a visit, whether it merges a
previously separate exact RHS or appends and merges a fresh row. The
driver scans even when no fuel remains. It reports `.fixed` when the
scan finds no enabled site and `.exhausted` when an enabled site remains
after the last unit of fuel.

## Receipts and guarantees

A report records only the numeric addresses in chronological order and a
stop reason. With the same input, designated zero instruction and budget,
`check` rejects an over-budget trace, replays each address against the
then-current table, and checks the stop claim against the reconstructed
endpoint. Any enabled order can be replayed. `run_checked` proves that
the producer's report passes this checker.

- `enabled_spec` characterizes the exact structural witness.
  `check_fixed` proves that every match in the final table has a
  structurally matching RHS in its class. `check_normalForm` packages
  reachability and stability for the zero-sample visits using the
  [§4 normal-form interface](peggy-normal-forms.md). Every visit at
  a fixed state literally returns that state.
- `check_exhausted` proves that all fuel was used and the endpoint
  is not fixed. `check_size` bounds the final table by the original size
  plus the budget. `check_retains` preserves the old typed rows, numeric
  addresses, ordered roots, loop frame and existing class equalities.
- `replay_prefix` validates every prefix of an accepted replay.
  `replay_sound` and `check_sound` reuse semantic soundness of the
  individual visits. For the given model and input tuple, the source
  must have well-founded demand and valid classes, and the designated
  nullary count instruction must return defined zero. Figure 11 ordered
  observations, including bottom, agree at every index, and the target
  classes remain valid. Receipt checking itself is structural.

## Regressions and scope

Two initial sites share a missing RHS. The driver appends it for the
first site and reuses it for the second. Fuel one leaves an enabled site,
and the checker accepts the other visit order as well. Another fixture
starts with one sample of an outer θ whose initializer is an inner
same-loop θ. The first append creates a new sample of the inner θ, and
the second append samples its zero initializer. Two visits close the
resulting table; visiting only the initial site leaves the generated site
enabled. Both θ rows have live self-feedback.

This is a bounded current-table scan for one analysis. Each scan
enumerates the table and can scan it again for RHS coverage at each
match. The bound is on visits and added rows. Reachable stability here
does not require monotone simulation, which fails for the deterministic
reuse policy under the existing injective comparison. The result does
not imply order independence, eventual closure with any particular
budget, unbounded saturation termination, or extraction cost optimality.

[Executable definitions](../../Silmaril/SSA/Peggy/EPEG/Saturation/Extension/Dedup/Worklist/Defs.lean) ·
[Theorem header](../../Silmaril/SSA/Peggy/EPEG/Saturation/Extension/Dedup/Worklist/Thms.lean) ·
[Regressions](../../tests/ssa/PeggyEgg.lean)

```sh
lake build --wfail +Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist.Thms PeggyEggTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PeggyEgg.lean
lake env leanchecker --fresh Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist.Thms
lake env leanchecker tests.ssa.PeggyEgg
```
