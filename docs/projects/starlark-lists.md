# Starlark collection store

The store follows the same Bazel-team core dialect as the scalar API, at
specification commit `c0af0ea03dc90d3bbc021394b693e6957cc15030` (2026-02-06).
The SHA-256 of the raw `spec.md` is
`9e1e2b52717512968270bc99ca79aa8c9014df99a9befd0b47eed59c7c848597`.
[Specification][spec] · [Scalar API](starlark.md)

## Supported code and observations

`Silmaril.Languages.Starlark.Lists.Thms` exposes the resolved code, store,
denotation and operational rules. Resolved expressions cover the following families.

- Scalar values `None`, Booleans and exact integers, with resolved binding reads.
- List, tuple and dictionary displays, with arbitrary nesting. The compiler-facing
  dictionary entry spine builds from earlier entries to later entries.
- Subscript reads from lists, tuples, dictionaries, ranges and valid UTF-8 strings,
  slice reads from lists, tuples, ranges and valid UTF-8 strings, and the one-argument
  list method `append`.
- [List and tuple equality and membership](#list-and-tuple-equality-and-membership) over the admitted recursive value profile.
- [Dictionary equality](#dictionary-equality) by canonical keys and live values.
- [Dictionary membership](#dictionary-membership-and-lookup-profiles) by checked key lookup.

The statement forms are name and subscript assignment, evaluation for effects,
`pass`, and sequencing. `Lists.Iteration.Thms` adds function-body conditionals,
`for` over lists, tuples, dictionaries and ranges, `break`, `continue` and
`return`. Loop targets can be names or nested tuple/list patterns of names.
A bare return lowers to the scalar value `None`. The suite index
counts lexical loop depth and rules out unscoped `break` and `continue`.
Callers supply resolved binding slots and enforce source rules such as
single-assignment globals and function-only control. The scalar entry points
and theorem signatures from #2144 remain source-compatible.
[Code and store](../../Silmaril/Languages/Starlark/Lists/Defs.lean) · [Suites](../../Silmaril/Languages/Starlark/Lists/Iteration/Defs.lean)

An allocation gives each collection a fresh address in one heap. Name
assignment copies values and therefore preserves references. Address numbers
are internal to a particular heap. A future shared-syntax agreement theorem
can compare effects under a correspondence of reachable addresses.
Tuple fields are immutable, and a tuple can hold a reference to a mutable
collection. That collection can be updated through the reference.
[Identity][identity] · [Lists][lists] · [Tuples][tuples] · [Dictionaries][dicts]

List and tuple indexes accept integers in `[-length, length)`, with negative
indexes measured from the end. List and tuple elements evaluate left to right.
Indexed assignment evaluates its RHS before its receiver and index.
`append` selects the method on the receiver before evaluating its argument and
checks mutability after argument evaluation. A successful append returns
Starlark `None`. A failure retains the state reached by the preceding
operands. Error tags carry the relevant failure kind and may include the
index, address, key, or binding. A bad address or an address of the wrong
kind is a model error for malformed host-supplied states. Resolved code has
no address literal.
[Subscripts][index] · [Assignments][assign] · [Denotation](../../Silmaril/Languages/Starlark/Lists/Denotation/Defs.lean)

## List and tuple equality and membership

`Code.compare` admits `==`, `!=`, `in` and `not in` as resolved collection
expressions. Both operands are evaluated left to right, and an operand failure
retains its reached state. `AtomSafe.compare` admits a comparison of two
call-free atoms to the existing function lowering theorem. The text and checked
module source profiles have their own operator admission rules.
[Comparisons][comparisons] · [Membership][membership] · [Resolved code](../../Silmaril/Languages/Starlark/Lists/Defs.lean)

An equality test admits nested lists, tuples and dictionaries, strings and scalar values
(`None`, Booleans, exact integers and binary64). Scalar leaves use the exact
numeric comparator, including mixed int/float and Boolean distinctions.
When both values belong to this profile, different types other than mixed
numbers compare unequal. Two sequences of the same kind read their live cells
left to right, check length, then test corresponding fields in order. Sequence
membership tests each field as the left operand of equality with the needle.
Length mismatch, first unequal field and first
membership hit stop their respective traversals. A reached out-of-profile value
produces a type error. A reached malformed sequence address produces the
corresponding store error. The comparison only reads the heap after evaluating
its operands, so it sees preceding mutations and preserves the reached state
on success or error.
[Exact scalar comparison](starlark-builtins.md#scalar-numeric-comparison) · [Rules](../../Silmaril/Languages/Starlark/Lists/Comparison/Operational/Defs.lean)

`scans_iff_scan` proves agreement for the reusable ordered traversal given
agreement for an individual test. `equalAt_iff`, `containsAt_iff` and
`tests_iff_evaluate` lift that agreement through nested fields and the four
operators. `eval_iff_denote` covers the exact result and whole reached state
after evaluating both operands. A fixture compares and looks up separately
allocated nested tuples with equal numeric leaves, and checks that their
canonical key encodings agree. Comparison reads the actual fields, independently
of the dictionary cache. Aggregate ordering, membership in other containers
and source admission for these operators remain open.
[Theorems](../../Silmaril/Languages/Starlark/Lists/Comparison/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Lists/Comparison/Checks.lean)

The comparison budget models the pinned Go default of 10. Every reached
equality comparison needs a positive budget, and each nested pair of sequence
fields consumes one level. Nine singleton levels followed by a scalar can
compare successfully. Ten such levels reach a depth error at the scalar.
Membership starts a fresh budget for each candidate and stops on the first
error or hit. Equal addresses still traverse fields. The pinned Go controls
confirm a list containing NaN compares equal to itself, while a reached
self-cycle or mixed list–tuple cycle reports a depth error. An earlier length
or field mismatch can leave the cycle unreached. The spec gives no depth
limit. Go’s limit is configurable. The dictionary key cache has its own
unbounded key-match policy.
[Go list membership and comparison][go-list-compare] · [Go sequence fields][go-slice-compare] · [Go tuple membership][go-tuple-has] · [Go depth check][go-depth] · [Paired Go controls](../../scripts/starlark/binary64/check.go) · [Dictionary key policy](starlark-builtins.md#numeric-dictionary-keys)

## Dictionary equality

The spec requires equal item counts and matching key/value pairs. Resolved
`==` and `!=` read both dictionary cells in the heap reached after operand
evaluation, left before right. After checking the sizes, they walk the left
table in insertion order. Each step looks up the stored canonical key code
in the right table, then compares the reached values with one less depth level.
A missing key, unequal value or error ends the scan immediately. An earlier
mismatch can leave a cycle unread. Reversing the operands can expose that cycle
when the other insertion order puts it first. Aliased dictionary cells still
traverse their entries. The comparison reads no mutable state outside the
supplied heap and preserves the entire reached state.
[Spec][dicts] · [Pinned Go rules][go-dict-equal] · [Independent rules](../../Silmaril/Languages/Starlark/Lists/Comparison/Operational/Defs.lean)

`looksUp_iff_findEntry` connects the operational key search to the table's
existing lookup. Under `UniqueKeyCodes`, `findEntry_some_iff_of_unique`
identifies the selected entry by membership and code equality, independent of
its position. The checked display append and subscript replacement or insertion
preserve unique codes. Normal insertion computes the code with `State.keyOf`.
Raw heap constructors supply their own table entries and tuple caches, so the
language interpretation assumes those entries have valid codes and unique
keys. Exact rule and denotation agreement also covers the first cached match
on raw tables. `equalAt_iff` lifts lookup agreement through bounded recursive
values, and `eval_iff_denote` covers operand effects, including a right operand
that mutates a value reachable from the left dictionary.
[Key and comparison theorems](../../Silmaril/Languages/Starlark/Lists/Comparison/Thms.lean) · [Lean checks](../../Silmaril/Languages/Starlark/Lists/Comparison/Dictionary/Checks.lean)

Value comparison uses the enclosing budget minus one. Key selection uses the
canonical profile described below. Aggregate ordering and text admission
remain separate.
[Dictionary lookup profiles](#dictionary-membership-and-lookup-profiles)

## Dictionary membership and lookup profiles

Resolved `in` and `not in` implement the checked canonical profile. After
both operands evaluate, the lookup reads the receiver, encodes the key with
`State.keyOf`, and selects the first matching entry. A successful lookup
reports presence or absence. An unhashable key is an error even on an empty
dictionary, and errors from reached heap reads propagate. `not in` negates
only a successful result. Membership leaves entry values unread, including
cycles. `dictionaryLookup_iff` proves agreement for the raw lookup, and
`containsAt_iff` and `eval_iff_denote` cover the Boolean operation and the
exact reached state. The spec identifies dictionary members as keys and
describes unhashable key use as a dynamic error. The checked profile applies
that error policy to membership.
[Spec membership][membership] · [Spec dictionary keys][dicts] · [Lookup rules](../../Silmaril/Languages/Starlark/Lists/Comparison/Operational/Defs.lean)

Pinned Go `Get` hashes the query first, even for an empty table. It then
walks the selected bucket and its overflow chain in slot order, testing only
candidates with the same stored hash. Each reached candidate uses Go `Equal`
with the default comparison limit of ten, independent of any enclosing
dictionary value comparison. Hash or comparison errors exit raw `Get` with
`found == false`. Both Go mapping membership and dictionary equality discard
that error and observe a miss. Go's negated membership complements that miss.
Dictionary equality still propagates errors from the reached values of keys
that were found.
[Go lookup][go-key-lookup] · [Go depth check][go-depth] · [Go mapping membership][go-mapping-membership] · [Go dictionary equality][go-dict-equal]

Ten singleton tuple levels around a scalar can make Go report an absent key
that the canonical cache matches. With a cyclic value behind that key, Go
dictionary equality can return `False` while Lean reaches the value depth
error. The pinned controls also verify that the deeply nested keys built from
`0` and `2^32` have different canonical codes yet collide in Go. Raw Go `Get`
reaches a depth error on that unequal candidate, and membership observes a
miss. Full raw-lookup agreement needs Go's hash and bucket selection, including
its runtime-seeded string hash and candidate slot order.
[Go integer hash][go-int-hash] · [Go string hash][go-string-hash] · [Paired Go controls](../../scripts/starlark/binary64/check.go)

`probesKeys_iff` stages an exact bounded key probe given an already selected
candidate order. Its key comparator covers scalars, strings and tuples of
those values. `probe_cached` identifies the normal canonical search as a
specialization of the ordered probe with the total code test. `lookupOrMiss`
preserves a hit and projects a raw error to a miss. The fixtures exercise
this projection for the deep-key cyclic-value case. Canonical equality and
membership still use cached keys. A full Go profile needs verified hash
results, ordered candidate selection and identity comparison for function
and builtin key leaves.
[Theorems](../../Silmaril/Languages/Starlark/Lists/Comparison/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Lists/Comparison/Dictionary/Checks.lean)

## Dictionary keys and order

Dictionary displays evaluate each key and then its value. The pair is checked
for admissibility and duplicates before evaluating the next pair. A subscript
write inserts a missing key at the end or updates the value in place, keeping
the original key and position. A missing subscript read fails.
`putEntry_keys` proves the resulting order of keys for both insertion and
replacement. The model uses an ordered list of entries.
[Dictionary expressions][displays] · [Dictionaries][dicts] · [Theorems](../../Silmaril/Languages/Starlark/Lists/Thms.lean)

Key comparison uses tagged scalar values and structural tuple contents. A
tuple's cached encoding brackets the encodings of its elements and is present
when every element has a key encoding. Separately allocated tuples with equal
contents hit the same entry. Boolean and numeric keys are distinct. List and
dict keys are rejected even when frozen, matching the pinned starlark-go
profile. The general prose spec allows for frozen mutable keys, so this policy
is explicit. The model covers the admissibility and equality needed by the
dictionary operations. The `hash` built-in and general value equality remain
open. Public raw heap constructors can supply malformed key caches. The
normal expression evaluator computes them on allocation.
[Lists][lists] · [Hashing][hashing] · [Pinned oracle][go]

## Reachable freezing

`State.freeze` is a host operation supplied with root values. It represents
the freezing part of publication. Module initialization and root selection are
outside this API. The reachable graph follows list and tuple elements and both
keys and values of dictionary entries. The implementation finds each selected
address at most once. Shared references, self-cycles, and cycles across
collection kinds all use this reachability policy. The heap keeps all addresses
and contents, and previously frozen cells stay frozen. Unreachable mutable
cells stay mutable. Reads continue to work through any alias.
[Freezing][freeze] · [Freeze definitions](../../Silmaril/Languages/Starlark/Lists/Freeze/Defs.lean)

`freezes_iff_freeze` independently characterizes the operation by live graph
reachability and the pointwise update on the original heap, for every finite
heap. `keyOf_freeze` proves that freezing preserves key eligibility and
encodings. `editCell_frozen` proves that a frozen cell rejects an edit with
its incoming state intact.
[Theorems](../../Silmaril/Languages/Starlark/Lists/Thms.lean)

## Iteration and control

A loop evaluates its iterable once. Lists and tuples capture their elements
and dictionaries capture their insertion-ordered keys. These collections
register their addresses on the iterator stack. A range uses a cursor
with its current integer, stride and remaining count. It has no heap address
to guard and produces elements on demand. List edits and dictionary
writes reject an active mutable address, so the guard applies through all
aliases. The frozen check retains priority over the active check. List
index validation precedes the write guard. Dictionary writes check
mutability before validating key admissibility, as in the Go oracle. The stack
has one entry per active iterator, including repeated entries for the same
object. Continue retains the entry until loop exit. Exhaustion, break, return
and error release the entry while retaining effects already performed. Nested
loops restore their incoming stack. The suite evaluator recurses on syntax
and the shared cursor evaluator recurses on the remaining count. Neither takes
execution fuel or bounds nesting.
[Iteration][iteration] · [For statements][for] · [Break and continue][break]

`eval_iff_denote` and `runs_iff_denoteSuite` prove exact agreement between the
respective denotations and independent big-step rules on success and failure,
including the resulting state. `cursor_eq_of_runs` and `cursor_runs_denote`
provide both directions of cursor agreement. The rules share cursor advancement
and lexical and heap primitives, and independently order their premises.
`iterators_denoteSuite` proves
restoration of the original iterator stack for every suite exit.
`editCell_iterating` states the active-iterator mutation guard.
[Expression rules](../../Silmaril/Languages/Starlark/Lists/Operational/Defs.lean) · [Suite rules](../../Silmaril/Languages/Starlark/Lists/Iteration/Operational/Defs.lean) · [Suite theorems](../../Silmaril/Languages/Starlark/Lists/Iteration/Thms.lean)

## Reproduction

```sh
lake build --wfail +Silmaril.Languages.Starlark.Checks +Silmaril.Languages.Starlark.Lists.Checks \
  +Silmaril.Languages.Starlark.Lists.Iteration.Checks +Silmaril.Languages.Starlark.Lists.DictionaryChecks \
  +Silmaril.Languages.Starlark.Lists.Comparison.Checks \
  +Silmaril.Languages.Starlark.Lists.Comparison.Dictionary.Checks
```

The kernel-checked fixtures cover addresses and aliasing, transitive freezing,
cycles, indexing and mutation failures, tuple keys, duplicate-key evaluation
order, insertion order, and iterator guards and cleanup. The Go fixtures use
`Program.Init` to observe state before publication and freeze selected roots.
Host appends and dictionary writes after a failed Starlark call test cleanup.
The reference is starlark-go at commit
`4f4267fb140d1e8b91c9bce55cee2f809e8840dd` with default syntax options. The
huge-index case compares failure only because Go reports its 32-bit conversion
limit.
[Lean fixtures](../../Silmaril/Languages/Starlark/Lists) · [Go fixture](../../examples/starlark/list-store/check.go) · [Pinned oracle][go]

Run the Go fixture from the public oracle checkout using Go 1.25 or newer.
Start these commands from the Silmaril repository root.

```sh
fixture="$(pwd)/examples/starlark/list-store/check.go"
oracle="$(mktemp -d)"
git clone https://github.com/google/starlark-go.git "$oracle"
git -C "$oracle" checkout --detach 4f4267fb140d1e8b91c9bce55cee2f809e8840dd
(cd "$oracle" && go run "$fixture")
```

## Remaining work

- **Functions.** User function objects, lexical cells, calls
  and declaration-based recursion checks extend this store. The call profile
  includes definition-time defaults, keyword-only parameters and both
  argument expansions and calls inside collection loops. Resolved nested
  call lowering covers call-free collection atoms, with general embedding
  into collection expressions still open.
  [Lexical calls](starlark-functions.md) · [Functions][functions]
- **Collection operations.** General equality and ordering, `hash`,
  concatenation, slicing of bytes, other methods, augmented forms beyond
  [integer subscript `+=`](starlark-functions.md#integer-augmented-subscript-assignment),
  destructuring with subscript or field leaves,
  general comprehension expression positions,
  and other iterable types remain open. The supported
  collection truth tests apply in the resolved suite conditional.
- **Module initialization and loading.** The finite manifest loads modules
  in their own lexical frames, freezes successful publication roots and
  preserves heap identities in the cache. Effectful host resolution and
  concurrency remain open. [Module loader](starlark-modules.md) · [Module execution][modules]
- **Source front end.** Parsing, shared Python and Starlark syntax resolution,
  and the Lean quotation macro remain open.

[spec]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md
[lists]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#lists
[tuples]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#tuples
[dicts]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#dictionaries
[comparisons]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#comparisons
[membership]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#membership-tests
[displays]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#dictionary-expressions
[identity]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#identity-and-mutation
[index]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#subscript-expressions
[assign]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#assignments
[freeze]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#freezing-a-value
[iteration]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#iteration
[for]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#for-statements
[break]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#break-and-continue
[hashing]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#hashing
[functions]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#functions
[modules]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#module-execution
[loading]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#load-statements
[go]: https://github.com/google/starlark-go/tree/4f4267fb140d1e8b91c9bce55cee2f809e8840dd
[go-list-compare]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/value.go#L1035-L1051
[go-slice-compare]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/value.go#L1053-L1075
[go-tuple-has]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/value.go#L1175-L1183
[go-depth]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/value.go#L1509-L1550
[go-dict-equal]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/value.go#L921-L951
[go-key-lookup]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/hashtable.go#L177-L201
[go-mapping-membership]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/eval.go#L1030-L1048
[go-int-hash]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/int.go#L183-L193
[go-string-hash]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/hashtable.go#L431-L450
