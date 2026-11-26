# Guarded PEG rewrite rules

The rules in `Silmaril.SSA.PEG.Rules.Thms` are equalities of Figure 11
values, including bottom. A client supplies the matched rows as `HasNode`
evidence and the guards listed below. For actual denotations,
`Graph.denote_solves` supplies the equations used by the rules. No matcher
is needed to state or prove a rule.
[Rule API](../../Silmaril/SSA/PEG/Rules/Thms.lean) · [Guarded semantics](peg-semantics.md)

## Definition 5.2

`InvariantAt` is the largest predicate that excludes theta at the designated
loop and is closed under the dependence edges of Definition 5.2. For that
loop, `eval` propagates only through its count and `pass` propagates through
no operand. Both omissions are captured by cutting sampling edges at
the designated loop. The proofs cover ordinary, initial, feedback and index
edges, and sampling at other loops. `denote_invariant` proves equality of
partial values when only the designated coordinate changes. At a cut, both
sample reads reset that coordinate to the same count. The remaining reads
use induction on well-founded Figure 11 demands, which also covers cyclic
PEGs. A semantic invariant can hold even when the syntactic check rejects it.
[Definition 5.2, p. 26](https://arxiv.org/pdf/1012.1802v3#page=26)

## Rule correspondence

Page numbers refer to arXiv:1012.1802v3, PDF SHA-256
`5bb3630c9a2a4766c5614b19148e865ee0797c693607b2cdd700b27c38df0b94`.

| Paper locator | Lean theorem | Premises and observation |
| --- | --- | --- |
| Fig. 11, p. 23 | `phi_true`, `phi_false` | A defined guard selects the corresponding arm. The other arm may be bottom. |
| App. A.1, p. 74 | `phi_same_of_defined` | Equal arms permit removal of the branch when the guard is defined at every index. |
| App. A.1, p. 74 | `phi_nested_true` | The two branches use the same condition. A bottom guard stays bottom. |
| Fig. 11, p. 23 | `theta_zero`, `theta_succ` | Read the initializer at count zero or the feedback at the previous count. Other coordinates are shared. |
| §5.3, p. 25 | `eval_zero`, `eval_zero_theta` | A defined zero count has an empty prefix. Sampling a theta at zero equals sampling its initializer at zero. |
| §5.3, p. 26 and App. A.1, pp. 73–74 | `eval_invariant` | The source is invariant in the sampled coordinate and the count is defined. A constant bottom stream is allowed. |
| §5.3, p. 26 and App. A.1, pp. 73–74 | `theta_self` | The initializer is invariant and the feedback stream equals the theta stream. Induction on the loop count eliminates the cycle. |
| §5.3, p. 25 | `pass_zero` | A true first sample exits at zero. This also applies to a theta with a true initializer. |
| §5.3, p. 25 | `pass_theta_false`, `pass_theta_false_succ` | A false initializer shifts the feedback pass by one and preserves bottom. The vertex equality uses a strict unary opcode with the stated natural-count interpretation. |
| Fig. 8(b–c), §3.3, pp. 16–17 | `pass_peel`, `pass_peel_phi` | The caller supplies a suffix reference whose samples match the original one iteration later. A defined zero and the successor contract build the actual lazy phi alternative. A bottom first sample blocks the exit. |

`StreamEq` compares typed references at every index. `streamEq_iff_vertex`
gives the same-sort equality plus heterogeneous value equality used by the
E-PEG receipt interface. Rules requiring definedness or shifted samples
need semantic evidence for those premises. An established stream equality
can supply the feedback premise of `theta_self`.

This slice leaves construction of peeled suffix graphs to callers. The
strength-reduction and arithmetic laws need separate model contracts for
machine overflow and partial operations. The fixture checks an invariant
eval over a varying theta, cyclic self-feedback, the Figure 8 pass equality,
and counterexamples to removing the definedness premises of equal-arm phi
and invariant eval. [Lean fixture](../../tests/ssa/PEGRules.lean)

```sh
lake build --wfail +Silmaril.SSA.PEG.Rules.Thms PEGRulesTests PEGCoreTests
lake env leanchecker Silmaril.SSA.PEG.Rules.Thms
lake env leanchecker tests.ssa.PEGRules
```
