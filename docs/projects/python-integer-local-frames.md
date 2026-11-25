# Python integer local frames

This slice adds a single frame with typed integer local slots, sequential
assignment, integer conditionals and return. It advances the statement and frame boundaries in
the [accepted P2/P3 plan](python-sos-acceptance.md). A compiler supplies a
`Code slots` body with `Fin slots` operands. The executable entry starts
each allocated slot unbound. The frame evaluates a closed arithmetic
right-hand side through the existing context selector or loads a local
slot. Binary right-hand sides can also combine local reads with arithmetic.
The left operand runs first and an operand error exits the pending calculation. A load of an unbound slot raises `UnboundLocalError`. A failed
right-hand side leaves every binding intact, including a previous value
of the assignment target. Successful writes affect only the target slot.
A conditional evaluates its test to an integer and enters the false branch
on zero and the true branch on a nonzero value. A failing test enters the
exception state before either branch. Branch choice leaves the store intact.
For integer `and` and `or`, the left operand determines whether the right
operand runs. The result is the selected integer operand.
[Definitions](../../Silmaril/Languages/Python/Core/Locals/Defs.lean)

The labelled steps expose writes for frame instrumentation and carry a
normal integer or uncaught exception at exit. The language observation
projects to the exit result. The frame retains its final store as evidence
for state preservation. The one-step selector agrees in both directions
with the relational rules. A decreasing work budget proves termination
and suffices for the bounded runner to return the structural specification's
exact result and store. Exhaustion with less fuel is a prefix status.
[Theorems](../../Silmaril/Languages/Python/Core/Locals/Thms.lean)

The compiler bridge can continue to target `Core.Body` for the existing
closed profile. A local-aware bridge can assign each resolved local a
stable slot and emit `Code slots` for this frame. A branch carries two
lowered continuations, each ending in its own return. The closed-return
compatibility theorem matches the existing Core observation after tagging
its exception. The Python/Starlark agreement remains stated for its original
Core profile.
Loops, globals, calls, handlers, multiple frames and host operations require
further coverage.

The public behavior is specified by the Python 3.12.13 Language Reference,
Execution model §4.2.2 and Simple statements §§7.2 and 7.6. The HTML SHA-256
digests are `1928f7f11bbb47a652c55a292cb90bbd5c07224e0c6ddf019445ae653cd64102`
and `817344777aad7579f74f9260bb2f41e3c8368ae5dce0fe083c2a458af3504721`
respectively. The frame decomposition follows the public architecture in
Köhl's thesis §4.4. [Execution model](https://docs.python.org/release/3.12.13/reference/executionmodel.html)
· [Simple statements](https://docs.python.org/release/3.12.13/reference/simple_stmts.html)
· [Thesis](https://arxiv.org/pdf/2109.03139v1)

Conditional evaluation follows Compound statements §8.1 and integer truth
follows Standard Types §Truth Value Testing. Their HTML SHA-256 digests are
`a52088b56170cf5ddafcb39451fc77d30b99940a07b5af0ce47f86c28364647f`
and `dd18748757c1fb19ab03068a9adfd8df2c66c2a1b6fb89d168723cede69ab242`
respectively.
[The if statement](https://docs.python.org/release/3.12.13/reference/compound_stmts.html#the-if-statement)
· [Truth value testing](https://docs.python.org/release/3.12.13/library/stdtypes.html#truth)
· [Boolean operations](https://docs.python.org/release/3.12.13/reference/expressions.html#boolean-operations)

The independently authored fixtures compare normal return after copying
and rebinding a local, read before write, failed reassignment and nested
arithmetic on local operands. Two opposing operand orders distinguish
an unbound read from division by zero. The CPython projection compares
the returned integer or exception class. The conditional cases cover
negative and zero conditions with a failing unused branch, and a failure
during the test. The Boolean-operation cases check when a right-hand
division runs and when the result preserves the left integer.
Internal write labels and the retained store are checked in Lean.
The tested CPython 3.12.13 distribution was the public Linux x86-64
python-build-standalone 20260807 release, asset SHA-256
`506191be3ee7bd190a8834dcdc1b3bc70aab50608deccc711935aa007239cabd`.
[Distribution](https://github.com/astral-sh/python-build-standalone/releases/tag/20260807)
· [Lean regression](../../tests/languages/python/locals/Regression.lean)
· [CPython oracle](../../tests/languages/python/locals/cpython_oracle.py)

```sh
lake build --wfail +Silmaril.Languages.Python.Core.Locals.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true --run tests/languages/python/locals/Regression.lean > /tmp/lean-locals.txt
python3.12 -I tests/languages/python/locals/cpython_oracle.py > /tmp/cpython-locals.txt
rg '^parity\t' /tmp/lean-locals.txt > /tmp/lean-locals-parity.txt
diff -u /tmp/cpython-locals.txt /tmp/lean-locals-parity.txt
```
