# Starlark universal built-in calls

This profile follows the Bazel-team specification at
`c0af0ea03dc90d3bbc021394b693e6957cc15030`. The raw `spec.md` SHA-256 is
`9e1e2b52717512968270bc99ca79aa8c9014df99a9befd0b47eed59c7c848597`.
[Built-in functions][builtins] · [Name resolution][names]

## API and observations

`Lists.Builtin.resolve` maps supported universal names to typed IDs after
lexical lookup has ruled out a shadowing binding. A resolved `Lists.Code.builtin`
expression denotes the first-class value for that ID. It can be stored,
captured, passed as an argument, called through a local binding, or used as a
dictionary key. Its key encodes the universal ID and its truth value is true.
It has no heap allocation or reachable cells of its own. The scalar resolver
and the existing resolved collection constructors retain their entry points.
[Shared value and syntax definitions](../../Silmaril/Languages/Starlark/Lists/Defs.lean)

The existing call evaluates the callee and operands left to right, expands
`*` and `**`, and dispatches on the resulting callable value. For these five
built-ins, a nonempty expanded keyword list fails before arity or operand
type checks. For example, an empty `**{}` expands to no keywords. Errors
carry the built-in ID and the offending keyword, arity bounds or value.
Earlier operand effects persist on failure, and the call destination is
written only on success. Built-in dispatch uses no lexical activation or
declaration-stack entry.
[Call definitions](../../Silmaril/Languages/Starlark/Functions/Defs.lean)

| Built-in | Positional arguments | Values and store |
| --- | --- | --- |
| `bool` | Zero or one | Existing truth rules for all supported values. The zero-argument result is `False`. |
| `len` | Exactly one | List or tuple length, dictionary entry count, or string byte length. Other represented types give a type error. |
| `type` | Exactly one | A string naming the existing value tag, including `NoneType`, `function` and `builtin_function_or_method`. |
| `list` | Zero or one | Allocates a fresh mutable list. The optional iterable is a list, tuple or dictionary. |
| `tuple` | Zero or one | Allocates an immutable tuple using existing key rules and the same iterable domain. Tuple addresses are internal. |

Dictionary iteration yields keys in insertion order. Both constructors make
shallow snapshots, retaining the identities of referenced elements.
Copying a frozen list can produce a mutable outer list with frozen elements
still shared. The built-ins only read input cells. They run no Starlark code
while copying, and leave the active-iterator stack alone. The three
inspection built-ins leave the heap alone after operand evaluation.
[Built-in definitions](../../Silmaril/Languages/Starlark/Functions/Builtins/Defs.lean)

`Builtins.invoke` is total over expanded arguments and the current state.
`invokes_iff_invoke` proves its exact result, error and store agree with the
independent built-in rules. These rules compose with operand evaluation and
call dispatch in `exec_iff_denoteBody`. No fuel or host callback is needed.
[Operational rules](../../Silmaril/Languages/Starlark/Functions/Builtins/Operational/Defs.lean) · [Theorem header](../../Silmaril/Languages/Starlark/Functions/Builtins/Thms.lean)

## Dialect and coverage

The spec permits 8-bit or 16-bit string elements. This profile selects
UTF-8 byte lengths, as pinned starlark-go does. For example, `len("é😀")`
is 6 in both. The Lean input uses Unicode text, while Go strings can also
hold invalid encodings. Both reject plain strings as iterable constructor
inputs. Keyword-before-arity rejection follows the pinned Go implementation.
The fixtures compare values, aliases and error categories. The existing
argument-signature and module-failure differences remain recorded in their
guides.
[Strings][strings] · [Pinned Go built-ins][go-library] · [Arguments](starlark-functions.md#argument-binding) · [Modules](starlark-modules.md)

The five implemented functions cover the represented values. Additional
collection or iterable types such as bytes, sets, ranges and iterable
views are open, as are floats and host values. The other pinned universal
functions are `abs`, `any`, `all`, `bytes`, `dict`, `dir`,
`enumerate`, `fail`, `float`, `getattr`, `hasattr`, `hash`, `int`,
`max`, `min`, `print`, `range`, `repr`, `reversed`, `set`,
`sorted`, `str` and `zip`. General bound-method dispatch is open. The
existing collection `append` primitive remains available through its
resolved collection syntax. The coverage guide lists the remaining methods.
[Coverage obligations](starlark.md#coverage-obligations)

## Checks

```sh
lake build --wfail +Silmaril.Languages.Starlark.Functions.Builtins.Checks
```

Run from the repository root with Go 1.25 or newer.

```sh
fixture="$(pwd)/examples/starlark/builtins/check.go"
oracle="$(mktemp -d)"
git clone https://github.com/google/starlark-go.git "$oracle"
git -C "$oracle" checkout --detach 4f4267fb140d1e8b91c9bce55cee2f809e8840dd
(cd "$oracle" && go run "$fixture")
```

[Lean fixtures](../../Silmaril/Languages/Starlark/Functions/Builtins/Checks.lean) · [Go fixtures](../../examples/starlark/builtins/check.go)

[builtins]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#built-in-constants-and-functions
[names]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#name-resolution
[strings]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#strings
[go-library]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/library.go
