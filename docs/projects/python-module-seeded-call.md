# Closed Python harness seeds

`Silmaril.Languages.Python.Core.Module.SeededCall` supplies a small
interpreter for an explicitly seeded module-call profile. A namespace has
separate lists for module globals and builtin bindings. Global reads
search the module first, including a present `None` value. A module write
preserves the builtin list. Lexically resolved local operands use bounded
slots in a separate frame. An unbound local raises `UnboundLocalError`.
[Definitions](../../Silmaril/Languages/Python/Core/Module/SeededCall/Defs.lean)
· [Theorem header](../../Silmaril/Languages/Python/Core/Module/SeededCall/Thms.lean)

## Callable and exception contract

An opt-in seed supplies typed values for the exception class and the two
helper callables. The interpreter dispatches the resolved value. A caller
can bind the same descriptor under another name or shadow the name in the
module. The ordinary module and closure entry points retain their own
initialization contracts.

The equality helper accepts two exact integers. Equality returns `None`.
Inequality raises `AssertionError` with a single integer-pair payload.
The expectation helper takes a supported exception class, a supplied
closed callable and its positional operands. It invokes that callable,
returns `None` after a matching raised error, and propagates an unmatched
error. If the callback returns normally, the expectation helper raises
its own assertion with the diagnostic selected by the seed. The preamble
uses a message. The SOS basis uses no argument. Recursive invocation
consumes the class and callback operands. The evaluator resolves the
callable before its arguments and evaluates arguments left to right.

The call model covers the closed helper descriptors and known non-callable
values in this value domain. Object equality, constructing an exception
instance by calling its class, arbitrary function callbacks, generalized
argument binding and an open exception hierarchy require a wider profile.
Unmodeled call shapes and operands return a separate unsupported result.
An expectation propagates that result. Invocations do not write either
namespace or perform host operations.

`invoke_iff` relates evaluation to the rules for decoded typed calls.
`Expectation.delivers_iff` verifies the exception boundary.
`Namespace.module_precedes`, `Namespace.builtin_fallback`, and
`Operand.eval_local` expose the lookup laws for lowering. The source
runner still needs an explicit bridge to this seeded profile.

## Distinct replay configurations

The corpus case comes from public revision
`b7ff99372dd24845cf84e58c96b877f15764b276` and has SHA-256
`822abc163f457af8784c41c08cef152ecbb1266bb9704197292944386bc3dd79`.
The raw module calls an assertion-raising helper through the seeded
expectation helper. The SOS basis supplies both helpers in its builtin
table. The legacy CPython runner prepends their definitions to the module
source. Stock Python supplies the `AssertionError` class and has no
helper bindings in either namespace.
[Public case](https://github.com/koehlma/rigorous/blob/b7ff99372dd24845cf84e58c96b877f15764b276/tests/python/programs/original/lambda-py/python-reference/exceptions/assertion-error.py)
· [SOS builtin basis](https://github.com/koehlma/rigorous/blob/b7ff99372dd24845cf84e58c96b877f15764b276/rigorous/semantics/python/basis/source/builtins.py#L1256)
· [CPython preamble and runner](https://github.com/koehlma/rigorous/blob/b7ff99372dd24845cf84e58c96b877f15764b276/tests/python/evaluation/run_cpython.py#L50)
· [Python name resolution](https://docs.python.org/release/3.12.13/reference/executionmodel.html#resolution-of-names)

| Configuration | Helper location | Observation |
| --- | --- | --- |
| Empty control | No helper bindings | `NameError` for the callable name |
| Stock subset control | No helper bindings | `NameError` for the callable name |
| Equivalent builtin seed | Supplied builtin table | Caught assertion with `None` result |
| Legacy preamble profile | Module global table | Caught assertion with `None` result |

The two seeded configurations match the selected call's completion.
They store helper bindings in different namespaces. The Lean fixtures
also check the local-slot boundary, a shadowed builtin, aliased calls,
different operands, the distinct assertion diagnostics, and unsupported
calls. This is scoped runtime evidence for a seeded call. It does not
extend the source corpus coverage count.
[Regression](../../tests/languages/python/module-seeded-call/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Languages.Python.Core.Module.SeededCall.Thms'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/languages/python/module-seeded-call/Regression.lean
```
