# Numbered-page computations

Import `Silmaril.Semantics.Page.Thms` and use the `Silmaril.Semantics.Page`
namespace. `Store Id Content Memory` supplies lookup and a point update with laws
for the selected page and every other page. `MapMemory` and `mapStore` give a
concrete model over functions. `Program` provides `pure`, `bind`, `choose`,
`read`, `write`, `allocate`, `deallocate` and an explicit divergent branch.
[`Defs.lean`](../../Silmaril/Semantics/Page/Defs.lean)

`Id`, `Content` and `Memory` are independent types. A client can share a `Model`
among several roots or structures, represent several ID spaces in `Id`, and
carry page tags in `Content` or metadata in its own `Memory`. The store laws
constrain the page lookup after updates. Clients supply their own invariants
for metadata, ownership, reachability, resource accounting and coordination.
The concrete model and image replay use `DecidableEq Id`. The abstract store and
ordinary execution require neither decidable equality nor finite domains.

## Ordinary execution

| Operation | Ordinary effect |
| --- | --- |
| `read p` | Returns the content of a defined page. Absent and UNDEF pages produce the distinct UB reasons `readAbsent` and `readUndef`. |
| `write p v` | Initializes or overwrites an allocated page with `v`. Writing an absent page produces `writeAbsent` UB. |
| `allocate` | Can choose any absent ID accepted by `Model.eligible` on the current allocated domain. Success returns `some p` and installs UNDEF at `p`. Exhaustion returns `none` and leaves memory intact. |
| `deallocate p` | Makes an allocated page absent. Deallocating an absent page produces `deallocateAbsent` UB. Eligibility can allow a freed ID to be allocated again. |

`Step` specifies each operation and emits an edit only on a successful update.
`Run` records the ordered edits of a maximal branch and a return with ordinary
final memory, UB, or explicit divergence. Each syntactic branch is
well-founded, and `run_exists` supplies at least one maximal outcome for every
input. Binary choice and fresh-ID choice are demonic. This calculus covers
sequential page effects with an explicit divergence outcome. General recursive
loops, small-step timing, concurrency, persistence, and any particular page
format are outside this model.
[`Thms.lean`](../../Silmaril/Semantics/Page/Thms.lean)

## Completions and observations

A completed image maps each allocated ID to a value, each absent ID to `none`,
and each defined ID to its existing value. `Completion` relates this image to
the ordinary memory. Execution always checks ordinary slots, so a completed
value cannot legalize a read from UNDEF. Replay starts with one initial image
and follows the same branch's edits in order. An allocation chooses a fresh fill
for that lifetime, a write replaces the fill, and a deallocation discards it.
Other entries retain their values. `step_completion` and `run_completion` prove
that replay tracks the allocated domain and preserves defined values.

The correctness predicates are pointwise in ordinary initial memory. For a
precondition `P`, quantify them as `∀ m, P m → ...`.

- `Correct` requires every ordinary branch to return normally and satisfy a
  postcondition on the returned value and ordinary final memory.
- `CorrectFrom` fixes an initial image. For each ordinary branch, it requires a
  normal return, at least one replay, and a postcondition that holds for every
  replay. The postcondition receives the return value, ordinary final memory,
  and completed final image. Supply `Completion` separately when using this
  judgment directly.
- `ExistsCorrect` chooses one valid initial image **before** quantifying over
  all ordinary branches and all the fresh fills in their replays.
- `ForallCorrect` requires a valid initial image to exist and applies
  `CorrectFrom` to every valid initial image. Together with the per-branch
  replay witness, this handles empty contents. An empty domain has a completion
  even when `Content` is empty. An initial UNDEF page or a branch that allocates
  a new page requires a value, even if that branch later frees the page.
  For subsingleton contents, the two completion quantifiers agree whenever
  either judgment holds.

`forallCorrect_of_correct` lifts ordinary correctness when every completion of
an ordinary final state satisfies the completed postcondition and contents are
inhabited. `ForallCorrect` implies `ExistsCorrect`. `correct_of_existsCorrect`
projects the latter to ordinary correctness with a final completion witness.
For inhabited contents all three coincide when the postcondition ignores the
completed image. Fully defined inputs give a unique initial image. When all
normal final memories are fully defined, all three agree on arbitrary final
image observations, for inhabited contents. Fresh allocation can introduce
UNDEF even from a fully defined input.

`correct_bind` composes ordinary judgments. `correctFrom_bind` passes the actual
intermediate image to the continuation. `existsCorrect_bind` requires that the
continuation accept every image the prefix can leave under its chosen witness.
A universally correct continuation is sufficient. `forallCorrect_bind` gives
this rule for universal prefixes. Two existentially correct segments can fail
to compose. The checked example returns a demonic bit in the prefix, keeps an
untouched UNDEF page, and asks for that bit to match the final completed value.
Each continuation can pick a matching image when started on its own. A single
initial image cannot match both prefix branches. This distinction needs no page
reads and is visible through the completed final image.
[`Examples/Thms.lean`](../../Silmaril/Semantics/Page/Examples/Thms.lean)

## Verification

Use the repository's pinned Lean toolchain for these commands.

```sh
lake build --wfail +Silmaril.Semantics.Page.Thms +Silmaril.Semantics.Page.Examples.Thms
make check CHECK_TARGETS='+Silmaril.Semantics.Page.Thms +Silmaril.Semantics.Page.Examples.Thms'
```

The examples check initialization followed by a legal read, a distinct UB
outcome for a forbidden read, exhaustion and reuse, empty contents, the effect
of inspecting the final image, and the existential sequencing counterexample.
