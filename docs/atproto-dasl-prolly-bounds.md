# Prolly bounds

## One layer

[`chunk_count`](../Silmaril/Semantics/Prolly/Bounds/Thms.lean) charges every
cut either to a full-width group or to a bucket hit. A possible final chunk
adds one. For `n` input keys and width `w`, it proves
`w * chunks ≤ n + w * hits + w` for every deterministic bucket function.

The explicit model selects a policy by drawing uniformly from a finite
nonempty sample space. Width is fixed and the level/key decision may depend
on the sample. For a **fixed** list of `n` keys at one level, a cap `p` on
the marginal hit probability of each key gives
`E[chunks] ≤ 1 + n/w + n*p`. The Lean theorem uses integer counts, avoiding
rounding or division by zero in its statement. Independence is not required:
linearity of the finite sum suffices, even for repeated keys or globally
correlated decisions. The fixture includes a bucket that shares one bit
across every key.

`uniform_adaptive_chunk_bound` allows a sample-dependent input list at a
fixed level. Condition on each realized list, using only the samples that
select that list. If every key in that list has a conditional hit cap `p`,
then `E[chunks] ≤ 1 + (1/w + p) * E[input length]`. The regression exhibits
unconditional hit probability `1/2` for each key but probability `1` for a
key selected using the same draw; the unconditional cap is not sufficient.

Both theorems are local to one layer.

## Whole-tree bounds

`promotions` projects the actual builder to separator keys. The proofs identify
the root level with the number of promotions and the unfolded block count with
one root plus the sum of non-initial frontier sizes. A root-only map, including an
empty map, emits one block. `frontierAt` pads the trajectory with empty lists
after its last frontier, so stopped samples pay no later cut cost.

`FrontierCap` conditions on the entire active frontier at each step. For cap
`p = numerator / denominator`, write `q = 2 / width + p`. If `q < 1` in a
nonempty uniform experiment, the expected number of non-root block occurrences
is at most `n * q / (1 - q)` and the depth tail satisfies
`Pr[depth > t] ≤ n / (width + 1) * q^t`. These are scaled natural inequalities
in Lean. The extra `1 / width` in `q` pays for the final chunk only on active
samples; this sufficient condition is not necessary (in particular, it is not
sharp for small widths).

These are bounds on the existing builder for the stated conditional model, not
claims that a concrete hash satisfies it. The proof does not bound distinct CID
bytes, incremental update locality, or expected depth by a closed log formula.
