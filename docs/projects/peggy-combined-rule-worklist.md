# Combined zero-sample and eval-scale worklist

The [zero-sample worklist](peggy-zero-sample-worklist.md) and the new
two-rule worklist use the same parameterized receipt driver. A driver
supplies a next-action search, a per-action enablement check, and a visit
on the existing typed E-PEG state. The checker replays the supplied tags
and addresses against the changing table, enforces the visit budget,
and independently checks the reported stop condition. The original
zero-sample interface still takes numeric sites.

## Included rules

- `zeroSample` uses the existing matcher and reuse policy for
  `eval ℓ (θℓ (initial, feedback), zero)`.
- `evalScale` uses the landed Figure 6(b→c) matcher and two-row plan
  for `scale(factor, eval ℓ (stream, count))`. A covered match already
  has an eval in the redex class with the same loop and count address.
  Its sampled row must have the same binary opcode and the precise
  ordered factor and stream addresses. The checker reads these rows
  from the current table. For an uncovered site the landed plan appends
  the binary row and eval, then joins the eval with the redex class.
  An exact RHS in a different class still takes this append path.

The producer scans zero-sample sites first, then eval-scale sites, in
address order within each tag. After a visit it searches the new
table. Each tagged visit costs one fuel unit, including an eval-scale
visit that appends two rows. Replay accepts other orders when each
tagged action is enabled at the point of use.

## Guarantees

`Combined.visit_sound` and `Combined.check_sound` preserve final class
validity and the original ordered Figure 11 observations, including
bottom at every result and index. For the given interpretation and
input, the original demands must be well founded and the original
classes valid. The designated zero opcode must return defined zero.
The designated factor must return a defined value, and scaling with
that value on the left must succeed for every defined right operand.
This last premise prevents code motion from introducing new bottom in
a sampled prefix. The executable receipt checks syntax and classes.
The two model laws are semantic premises of the theorem.

`Combined.check_fixed` proves that both enabled predicates are false
at every address of the checked final table. This concerns the two
included executable matchers and their coverage policies.
`Combined.check_exhausted` proves the budget was used and some action
is still enabled. Either accepted status gets the same preservation
theorem. `Combined.run_checked` connects the bounded producer to the
independent checker.

## Regression and boundary

The Figure 6 fixture includes an extra zero sample of the counter θ.
The first visit appends the zero-sample RHS. The next visit appends
and merges the scaled sample. The table grows from 9 to 12 rows and
preserves the repeated observation `[15, 3, 3, 15]`. One unit of fuel
leaves the eval-scale site enabled. The checker rejects that trace
labelled fixed, rejects a wrong tag, and accepts the two valid visits
in the reverse order.

The fixture uses two initially visible sites. With these exact
matchers, zero sampling appends only an eval, whereas an eval-scale
redex starts at a binary application. Eval-scale appends a binary
application and an eval that samples that application, whereas a
zero-sample redex needs an eval that directly samples a θ. Both visits
retain old row wiring. A rescan still matters for same-rule generation,
such as the existing nested zero-sample fixture.

This is bounded replay over two named rules. The interface makes no
claim of completeness of e-matching, unbounded termination, or
order-independent saturation.

[Receipt driver](../../Silmaril/SSA/Peggy/EPEG/Saturation/Extension/Worklist/Thms.lean) ·
[Combined rules](../../Silmaril/SSA/Peggy/EPEG/Saturation/Extension/Worklist/Combined/Defs.lean) ·
[Soundness and stop theorems](../../Silmaril/SSA/Peggy/EPEG/Saturation/Extension/Worklist/Combined/Thms.lean) ·
[Regressions](../../tests/ssa/PeggyEgg.lean)

```sh
lake build --wfail +Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Worklist.Combined.Thms PeggyEggTests PeggySimpleValidationTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PeggyEgg.lean
lake env leanchecker --fresh Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Worklist.Combined.Thms
lake env leanchecker tests.ssa.PeggyEgg
```
