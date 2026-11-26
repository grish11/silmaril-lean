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
`*` and `**`, and dispatches on the resulting callable value. For these
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
| `len` | Exactly one | List, tuple or range length, dictionary entry count, or string byte length. Other represented types give a type error. |
| `type` | Exactly one | A string naming the existing value tag, including `NoneType`, `function` and `builtin_function_or_method`. |
| `list` | Zero or one | Allocates a fresh mutable list. The optional iterable is a list, tuple, dictionary or range. |
| `tuple` | Zero or one | Returns an immutable tuple over the same iterable domain. The internal tuple cell carries its structural key when hashable. |
| `range` | One to three | Checks integer parameters in order, rejects a zero step, and returns an immutable range without allocating a heap cell. |
| `abs` | Exactly one | Returns exact integer magnitude or clears the sign of a binary64 input. Booleans and other nonnumeric arguments give a type error. |
| `any` | Exactly one | Returns `True` at the first truthy item of a list, tuple, dictionary or range. Exhaustion gives `False`. |
| `all` | Exactly one | Returns `False` at the first falsy item of the same iterable types. Exhaustion gives `True`. |

Dictionary iteration yields keys in insertion order. Both constructors make
shallow snapshots, retaining the identities of referenced elements.
Copying a frozen list can produce a mutable outer list with frozen elements
still shared. The built-ins only read input cells. They run no Starlark code
while copying, and leave the active-iterator stack alone. The three
inspection built-ins and `range` leave the heap alone after operand evaluation.
[Built-in definitions](../../Silmaril/Languages/Starlark/Functions/Builtins/Defs.lean)

## Materializing ranges

`list(range(...))` and `tuple(range(...))` consume the same exact cursor as
a function-body loop, in yield order. The cursor is collected only after
the operand and the call's expansion, keyword and arity checks succeed.
The constructor then adds one result cell using the existing list or tuple
allocation rule, including for an empty range. A rejected call retains
earlier operand effects and adds no result cell. The range is immutable,
and reading it changes neither the heap nor active iterator guards.
[Pinned list spec][list] · [Pinned tuple spec][tuple] · [Pinned Go list][go-list] · [Pinned Go tuple][go-tuple]

Materializing a range takes time and storage proportional to its length
in elements, with exact integer arithmetic for cursor steps. The denotation
terminates by the remaining count. There is no language-level size cutoff
or fuel error. Executing large materializations depends on host memory.
The Go implementations preallocate for their host-width range length.
The common-profile fixture uses small ranges, and the Lean fixture includes
a short range with exact endpoints outside Go's host integer width.
[Cursor definition](../../Silmaril/Languages/Starlark/Lists/Iteration/Defs.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Functions/Builtins/Checks.lean) · [Pinned Go fixtures](../../examples/starlark/builtins/check.go)

## Integer magnitude and iterable truth

`abs` uses arbitrary-precision integer magnitude. `any` and `all` acquire
the existing snapshot or range cursor after argument expansion, keyword and
arity checks. They truth-test one yielded value at a time, using dictionary
keys in insertion order. A decisive item ends the scan without advancing
again. The quantifiers read ranges lazily, with work proportional to the
number of cursor steps reached. String values can be truth-tested as items.
Plain strings are invalid iterator operands in the spec, Go and this profile.
[Pinned spec for abs][abs] · [Pinned spec for any and all][any] · [Pinned iteration rules][iteration] · [Pinned Go implementation][go-pure]

The builtin phase preserves the entire reached state. For represented
iterables the cursor and truth reads execute no user code, so they use the
incoming iterator stack throughout. Go acquires an iterator and calls
`Done` on both exhaustion and an early decision. The Go fixture observes
this through a host iterator and host `Truth` callbacks, which are outside
the Lean profile. On arbitrary resolved stores, a malformed receiver can
fail during acquisition, and a malformed collection item can fail when its
truth is read. The first reached read error keeps its category. The fixtures
check that a decisive item can leave a malformed tail unread.
[Operational scan rules](../../Silmaril/Languages/Starlark/Functions/Builtins/Operational/Defs.lean) · [Exact cursor and state theorems](../../Silmaril/Languages/Starlark/Functions/Builtins/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Functions/Builtins/Checks.lean) · [Go fixtures](../../scripts/starlark/builtins/check.go)

The pinned spec and Go agree on the results for the common input domain.
Go's positional unpacker rejects expanded keywords before arity and type.
The spec describes the results in terms of collection elements, while Go
accepts any value implementing `Iterable`, including element views and host
types. Sets, bytes, iterable views such as `string.elems()`, and host
values are absent from the Lean profile. Ranges use exact integers and
counts in Lean, and Go's range constructor uses host-width integers.
The fixtures compare range results within that shared domain and exercise
a larger lazy range only in Lean.
[Pinned spec for abs][abs] · [Pinned spec for any and all][any] · [Pinned Go argument checks][go-unpack] · [Pinned Go range][go-range]

## Resolved binary64 values

A resolved client can supply `Starlark.Value.float bits` through the scalar
value branch of the existing store. The `UInt64` is the binary64 interchange
encoding. Lean's structural equality distinguishes all different bit
patterns, including the two zero signs and distinct NaN payloads. This
low-dependency carrier preserves the same bits as Silmaril's IEEE `F64`.
[Value definitions](../../Silmaril/Languages/Starlark/Defs.lean) · [IEEE model](../../Silmaril/Numeric/Ieee754.lean)

`abs` clears the sign bit and preserves the exponent and fraction, including
a NaN's payload and quiet bit. Both zeros become positive zero, negative
infinity becomes positive infinity, and the largest finite magnitude stays
finite. This operation needs no rounding, overflow handling, or host
floating-point environment. The specification does not pin a NaN payload
policy for `abs`. The raw-bit rule follows pinned Go's `math.Abs`.
Both signed zeros are false, and every other encoding is true. The same
truth test applies in `bool`, `any`, `all` and existing conditionals.
`type` returns `"float"`. The operator rules characterize magnitude by
remainder modulo `2^63` and give exact truth results.
[Pinned floats][spec-floats] · [Pinned abs][abs] · [Go abs][go-abs] · [Operator theorems](../../Silmaril/Languages/Starlark/Binary64/Thms.lean)

## Scalar numeric comparison

The scalar evaluator uses language comparison for `==`, `!=`, `<`, `<=`,
`>` and `>=`. The two signed zeros compare equal. Every NaN compares equal
to every other NaN and greater than positive infinity. Negative infinity
is below every finite value. Booleans order as `False < True` and compare
unequal to numbers. Ordered Boolean–number comparisons give `binaryType`.
Structural Lean equality still distinguishes encodings for observations of
state and returned values.
[Pinned floating-point numbers][spec-floats] · [Pinned comparisons][spec-comparisons] · [Pinned Booleans][spec-booleans] · [Go scalar comparisons][go-compare]

Finite operands are compared in integer units of `2⁻¹⁰⁷⁴`, the least positive
binary64 value. A subnormal contributes its signed fraction. A normal with
encoded exponent `e` contributes its signed significand times `2^(e-1)`.
An integer contributes its exact value times `2^1074`. This gives exact
mixed comparison even above `2^53`. The operational field rules reconstruct
the original sign, exponent and fraction. Separate comparison rules derive
an order and interpret the operator. `decodes_iff_decode` and
`orders_iff_compareNumbers` give agreement on the intermediate observations.
`compares_iff_applyBinary` and `eval_iff_denoteExpr` give agreement on the
result or error, including left-to-right operand evaluation.
[Binary64 theorems](../../Silmaril/Languages/Starlark/Binary64/Thms.lean) · [Scalar theorems](../../Silmaril/Languages/Starlark/Thms.lean) · [Pinned Go controls](../../scripts/starlark/binary64/check.go)

## Numeric dictionary keys

An integer or binary64 key encodes the exact comparison observation. Finite
codes use signed `2⁻¹⁰⁷⁴` units, each infinity has its own tag, and NaN codes
share one tag. Booleans have a separate code from every number.
`scalar_key_eq_iff_eq` proves equality of scalar key encodings exactly when
language `==` returns `True`. `scalar_key_match_iff_eq` gives the same result
for the Boolean test that dictionary lookup and replacement use.
[Pinned dictionaries][spec-dicts] · [Pinned hashing][spec-hashing] · [Key theorems](../../Silmaril/Languages/Starlark/Lists/Thms.lean)

Updating through an equivalent key keeps the original displayed key and
its iteration position. The fixtures check the original signed-zero and
NaN bits, and lookup through both an integral float and its equal integer.
Tuple allocation composes the field codes in its cached encoding. Nested
tuples therefore match when their corresponding numeric fields compare
equal, and an unhashable list field still makes its enclosing tuple
unhashable. General aggregate comparison and membership remain outside this
profile.
[Pinned Go replacement][go-key-insert] · [Lean fixtures](../../Silmaril/Languages/Starlark/Binary64/Checks.lean) · [Go controls](../../scripts/starlark/binary64/check.go)

Go uses hash buckets followed by numeric equality, so `1` and `1.5` can
share a hash and still occupy separate entries. The Lean store tests
canonical codes in its entry list and gives no language `hash` operation.
Both reject an equivalent second key in a dictionary display, as the
spec requires. Go writes the second value into its private dictionary
before raising the duplicate error. The Lean evaluator retains the first
value in the accepted prefix of the reached heap. With Go's default
comparison depth limit of 10, a lookup through ten nested singleton tuples
can fail before comparing their numeric leaves. Lean compares the flattened
cache without a recursive comparison depth limit.
[Pinned display rules][spec-dict-display] · [Pinned Go display][go-key-display] · [Go float hashing][go-float-values] · [Go comparison limit][go-key-depth]

The `float()` conversion, source literals and float arithmetic require
separate rules. The Go controls distinguish finite-input conversion overflow,
which gives an error, from explicit infinity and arithmetic overflow, which
can give infinity. The Lean slice only observes an already supplied encoding.
[Go conversion][go-float] · [Pinned float conversion][spec-float-conversion] · [Go controls](../../scripts/starlark/binary64/check.go)

## Agreement

`Builtins.invoke` is total over expanded arguments and the current state.
`invokes_iff_invoke` proves its exact result, error and store agree with the
independent built-in rules. Range materialization uses `CursorCollects`,
whose yield order agrees with collection by `cursorCollects_iff_collect`.
`truthScans_iff_truthCursor` gives both directions for cursor exhaustion,
continuation, a decisive item or the first truth-read failure.
`exec_iff_denoteBody` composes builtin dispatch with ordered callee evaluation,
operand evaluation and expansion in resolved calls, including checked
expression operands. `lower_preserves` preserves the exact heap and visible
bindings under scratch projection.
[Operational rules](../../Silmaril/Languages/Starlark/Functions/Builtins/Operational/Defs.lean) · [Built-in theorem](../../Silmaril/Languages/Starlark/Functions/Builtins/Thms.lean) · [Cursor theorem](../../Silmaril/Languages/Starlark/Lists/Iteration/Thms.lean) · [Lowering theorem](../../Silmaril/Languages/Starlark/Functions/Lowering/Thms.lean)

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

Calls can [spread ranges as positional arguments](starlark-functions.md#argument-binding).
Loops can [unpack items into nested name patterns](starlark-functions.md#loop-target-patterns).
Additional value types include bytes, sets, iterable views and host values.
The other pinned universal
functions are `bytes`, `dict`, `dir`,
`enumerate`, `fail`, `float`, `getattr`, `hasattr`, `hash`, `int`,
`max`, `min`, `print`, `repr`, `reversed`, `set`,
`sorted`, `str` and `zip`. General bound-method dispatch is open. The
existing collection `append` primitive remains available through its
resolved collection syntax. The coverage guide lists the remaining methods.
[Lazy range subscript reads](starlark-functions.md#lazy-range-subscript-reads) · [Coverage obligations](starlark.md#coverage-obligations)

## Checks

```sh
lake build --wfail +Silmaril.Languages.Starlark.Functions.Builtins.Checks \
  +Silmaril.Languages.Starlark.Binary64.Checks
```

Run from the repository root with Go 1.25 or newer.

```sh
repo="$(pwd)"
oracle="$(mktemp -d)"
git clone https://github.com/google/starlark-go.git "$oracle"
git -C "$oracle" checkout --detach 4f4267fb140d1e8b91c9bce55cee2f809e8840dd
(cd "$oracle" && go run "$repo/examples/starlark/builtins/check.go" &&
  go run "$repo/scripts/starlark/builtins/check.go" &&
  go run "$repo/scripts/starlark/binary64/check.go")
```

[Lean fixtures](../../Silmaril/Languages/Starlark/Functions/Builtins/Checks.lean) · [Go call and constructor fixtures](../../examples/starlark/builtins/check.go) · [Go magnitude and truth fixtures](../../scripts/starlark/builtins/check.go) · [Go binary64 controls](../../scripts/starlark/binary64/check.go)

[builtins]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#built-in-constants-and-functions
[names]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#name-resolution
[strings]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#strings
[list]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#list
[tuple]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#tuple
[abs]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#abs
[any]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#any
[iteration]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#iteration
[go-list]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/library.go#L679-L696
[go-tuple]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/library.go#L1124-L1143
[go-pure]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/library.go#L179-L227
[go-unpack]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/unpack.go#L207-L239
[go-range]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/library.go#L827-L879
[go-library]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/library.go
[spec-floats]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#floating-point-numbers
[spec-comparisons]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#comparisons
[spec-booleans]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#booleans
[spec-dicts]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#dictionaries
[spec-hashing]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#hashing
[spec-dict-display]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#dictionary-expressions
[spec-float-conversion]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#float
[go-abs]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/library.go#L178-L195
[go-float-values]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/value.go#L473-L521
[go-compare]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/value.go#L1547-L1609
[go-float]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/library.go#L391-L446
[go-key-insert]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/hashtable.go#L78-L143
[go-key-display]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/interp.go#L473-L486
[go-key-depth]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/value.go#L1511-L1550
