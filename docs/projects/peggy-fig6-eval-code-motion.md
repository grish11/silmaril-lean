# Figure 6(b–c) code motion through eval

This development checks the first rewrite in §3.1, Figure 6(b→c),
printed p. 15 of arXiv:1012.1802v3. The example moves the multiplication
by five through the eval at a loop's exit. The rewrite is the
invariant-operand push-through-eval rule in Appendix A.1, printed p. 74.
The versioned PDF has SHA-256
`5bb3630c9a2a4766c5614b19148e865ee0797c693607b2cdd700b27c38df0b94`.
[Figure 6](https://arxiv.org/pdf/1012.1802v3#page=15) ·
[Appendix A.1](https://arxiv.org/pdf/1012.1802v3#page=74)

## Checked rewrite

The [matcher](../../Silmaril/SSA/Peggy/Worked/EvalScale/Defs.lean) checks a
specified binary count operator with the designated nullary factor row on
the left and an actual eval row on the right. The nullary row fixes the
factor at every index. The dialect contract `Law` supplies its defined
value and totality of the binary operator at that left value for every
defined right value. The worked model uses pure natural-number arithmetic
with a defined five literal and multiplication.

Figure 11 eval samples only when its count is defined, and propagates
bottom from any earlier sample. Moving a strict operation through eval
requires that the operation preserve that prefix-definedness test.
`commute` proves this using totality at the fixed operand. A bottom in the
input stream or count still produces bottom. The same count row and loop
coordinate are used on both sides. The proof uses the original figure's
prefix semantics over the unbounded iteration index, independently of
the fixture's concrete exit count.

The executable construction first appends the inner product and then an
eval of that new row. The second append runs the existing E-PEG worklist
with one guarded merge and one unit of merge fuel. `Match.equation_holds`
justifies the merge in every model satisfying `Law`.
Extraction redirects the matched root occurrences to the new eval.
The existing selection checker verifies the supplied rank on the
actual candidate, ordered root classes, and the unchanged retained
rows with their ordered operands. No row deletion is performed.

## Worked observation

The cyclic fixture supplies the exit predicate omitted in the paper
drawing. It builds the counter `θ(0, succ(counter))` with
`pass(counter ≥ 3)`, giving a sampled count of three. Both generated
rows are absent initially. The regression checks replay budgets of zero,
one, and two appends, the joined class, candidate wiring, and rejection
of an empty target rank. The accepted candidate redirects two ordered
occurrences of the scaled result. Lean proves the exact ordered Figure
11 outputs `[15, 3, 3, 15]` at every index.

The matcher rejects replacing the invariant factor row with the loop
counter. A second interpretation uses the same literal and counter, but
the product returns bottom on right operand zero. The source still
observes 15, since it multiplies only the sampled value three.
Multiplying before eval makes sample zero bottom, so the mapped prefix
test rejects the later sample. The regression checks this using the
native counter stream. The partial interpretation violates `Law`.

The observation theorem concerns pure typed PEG counts, a Boolean exit
predicate, and ordered partial values. This covers Figure 6(b→c).
The later strength reduction in Figure 6(d), the CFG reversion in
Figure 6(e), profitability, Java arithmetic and overflow, exceptions,
and heap or alias behavior remain outside the modeled fragment.

```sh
lake build --wfail +Silmaril.SSA.Peggy.Worked.EvalScale.Thms PeggyEggTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PeggyEgg.lean
lake env leanchecker --fresh Silmaril.SSA.Peggy.Worked.EvalScale.Thms
lake env leanchecker tests.ssa.PeggyEgg
```
