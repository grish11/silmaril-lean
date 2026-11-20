# A probabilistic bound for one Prolly layer

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

This does not yet bound the height, total number of blocks, or edit cost of
the whole randomized tree. Later levels have sample-dependent inputs. A
whole-tree result needs a conditional model for newly reached levels and
separate stopping-time or summation arguments; fixed-input marginals alone
do not justify those claims.
