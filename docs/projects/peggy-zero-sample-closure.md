# Checked zero-sample reuse and finite site closure

The [deduplication pass](../../Silmaril/SSA/Peggy/EPEG/Saturation/Extension/Dedup/Defs.lean)
runs §5.3's zero-sample-through-θ analysis at a supplied list of numeric
site addresses. It keeps the [fresh-append analysis](peggy-node-extension.md)
available as a separate transition.

## Checker and transition

The existing matcher binds the redex to
`eval ℓ (θℓ (initial, feedback), zero)`. The RHS check binds an actual row
to `eval ℓ (initial, zero)` with the same result sort, loop identity,
and exact ordered operand addresses. Operand classes alone cannot
satisfy this check. The coverage check additionally requires the RHS
row and redex to be in the same class. `checkRhs_iff` and
`checkCovered_iff` prove both directions of these specifications.
The executable pass requires decidable equality for data sorts and the
nullary count opcodes used by the redex matcher.

1. When any exact RHS is in the redex class, the visit returns the
   identical state.
2. Otherwise, when an exact RHS exists, the visit reuses the first in
   numeric address order and joins its class with the redex class using
   the existing whole-class merge.
3. When no exact RHS exists, the visit runs the existing append receipt
   and its single checked merge. An out-of-range address or a row that
   fails the redex matcher also leaves the state unchanged. These sites
   do not pass the completion check.

`ensure_sound` and `close_sound` use well-founded source demands and a
valid source partition for the given interpretation and input tuple.
The designated nullary count operation must return defined zero.
The same Figure 11 rule justifies both the reuse merge and the append
receipt. The initializer and feedback can be partial. The theorems
establish final class validity and equality of ordered Figure 11
observations, including bottom, at every index.

## Fixed site scope

`close` makes one pass over the supplied list and appends at most one
row per occurrence. `close_size` bounds the result by the original
table size plus the list length. `close_retains` embeds the original
typed graph and class equalities at unchanged numeric addresses.

`close_checked` assumes every listed site has a redex witness in the
input table. It proves that the executable checker accepts all those
sites after the pass. A successful visit establishes an exact RHS in
the site class. Subsequent appends preserve row shapes and addresses,
and subsequent merges preserve established same-class pairs. Initial
eligibility and completed witnesses thus survive every later visit.
`visit_stutters` and `close_fixed` show that each completed visit
and a repeat of the whole list return the identical state. Duplicate
sites in the list are allowed.

The cyclic fixture has two redexes with the same initially absent RHS.
The first visit appends that RHS, the second reuses it and merges its
previously separate class, and the finished list stutters. The fixture
checks that the graph grows from six to seven rows and that the ordered
roots and bottom observations are preserved.

## Comparison boundary

The pass only checks closure for the supplied eligible sites. A fresh
RHS can itself become a redex when its sampled initializer is another
same-loop θ. Such new sites stay outside the frozen list.

The [fresh-append simulation](peggy-node-monotonicity.md) maps a newly
added row to a newly added row. Reuse can produce a successor without
that fresh address, and an injective extension of an existing map
cannot use an address already assigned to a different source row.
The regression gives two comparable states with two exact RHS rows
anchored by distinct ordered roots. The smaller state merges the first
with the redex. The larger state already covers the redex with the
second and stutters. Any embedding of the successors would have to
preserve the ordered root addresses, and the larger partition lacks the
chosen class pair. This refutes monotone simulation for this deterministic
policy under the existing embedding comparison. The fixed-scope theorem
uses direct preservation of completed sites. Monotonicity under another
comparison or reuse policy and closure over newly exposed sites remain
open.

[Theorem header](../../Silmaril/SSA/Peggy/EPEG/Saturation/Extension/Dedup/Thms.lean)

```sh
lake build --wfail +Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Thms PeggyEggTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PeggyEgg.lean
lake env leanchecker --fresh Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Thms
lake env leanchecker tests.ssa.PeggyEgg
```
