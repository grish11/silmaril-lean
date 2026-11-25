# Evaluation contexts for Python Core

This P2 increment of the [accepted execution plan](python-sos-acceptance.md)
separates evaluation position from primitive contraction in the closed
arithmetic core. A context is a list of expression frames in root-to-redex
order. The right-operand frame carries an evaluated left integer. The
left-operand frame retains the unevaluated right expression. The selector
returns either an integer value or the uniquely positioned arithmetic
redex. A successful contraction plugs its result back through the frames.
A division error discards all pending arithmetic frames.
[Context definitions](../../Silmaril/Languages/Python/Core/Context/Defs.lean)

The proofs reconstruct the input expression from its decomposition, show
that plugging any redex into a legal context identifies the same focus,
and prove that decomposition and relational contraction give exactly the
old expression steps. The executable selector agrees with the existing
reducer. At the Core machine boundary it preserves the precise action and
successor on every state. The fixture covers nested left and right
positions, a signed quotient, and exception propagation through two frames.
[Theorems](../../Silmaril/Languages/Python/Core/Context/Thms.lean)
· [Regression](../../tests/languages/python/context/Regression.lean)

The compiler can continue to emit the existing `Core.Body`. Clients can
select or replug the next arithmetic operation without changing entry
policy or exit labels. The Python/Starlark agreement uses those same
Core definitions. The next stateful slice can reuse this arithmetic path
while supplying local slot reads, assignment and frame entry separately.
This slice models expression frames within one closed expression.

The context decomposition follows the architecture in Köhl's thesis,
§4.3.1, with the left-to-right order and integer operations of the Python
3.12.13 Language Reference, §§6.7 and 6.16. The arXiv v1 PDF has SHA-256
`104b05eaa440d07e41787e2b6648ce5f066bcdd65d70178630da2933b8071221`.
The Expressions HTML has SHA-256
`d8c992b1815b59ba65aa9a0144bf2f0a24a3551cda8cbb06f5e76c5caec7d994`.
[Thesis](https://arxiv.org/pdf/2109.03139v1)
· [Expressions](https://docs.python.org/release/3.12.13/reference/expressions.html)

```sh
lake build --wfail +Silmaril.Languages.Python.Core.Context.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/languages/python/context/Regression.lean
```
