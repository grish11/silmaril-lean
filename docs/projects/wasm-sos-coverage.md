# Guarded Wasm SOS correspondence

Each row identifies a checked domain and its native dialects. Rows use V1, Lime1,
and Core unless they specify a narrower set.
The SOS rules and their native renderings live under
[`Silmaril.Wasm.Institution.Operational`](../../Silmaril/Wasm/Institution/Operational).
Readback starts from a rendered source and allows any native successor or finite
endpoint. The exact store, frame, and instruction list are part of the
reconstructed target. See the linked theorem headers for the host, typing, and
allocation premises.

| Slice | Checked boundary | Remaining cases |
| --- | --- | --- |
| [Integer division](../../Silmaril/Wasm/Institution/Operational/LegacyDivision/Transport/Thms.lean) | Flat signed and unsigned division at each width, including a zero divisor and signed overflow traps. | Other flat numeric operators and division in general structured code. |
| [Numeric locals](../../Silmaril/Wasm/Institution/Operational/Locals/Native/Thms.lean) | Typed flat `local.get`, `local.set`, and `local.tee` with exact local updates. | Uninitialized and nonnumeric Core local slots, globals, and arbitrary structured contexts. |
| [Scalar blocks](../../Silmaril/Wasm/Institution/Operational/Blocks/Native/Thms.lean) and [nested branch exits](../../Silmaril/Wasm/Institution/Operational/BranchExit/Native/Thms.lean) | An isolated scalar block with flat locals and normal exit. A separate guard covers `br 1` followed by `br 0` under two already-entered block labels. | Nested source entry, `br_if`, `br_table`, and loop continuations. |
| [Checked indexed blocks](../../Silmaril/Wasm/Institution/Operational/Blocks/Indexed/Native/Thms.lean) | Core and Lime1 resolve a numeric signature in the current frame module. The standalone slice covers flat local code, immediate `br 0`, and immediate function return. The ranked graph below also checks indexed blocks, conditionals, and loops. | Nonnumeric signatures and whole-module validation. V1 admits only unindexed, parameterless structured labels with at most one result. |
| [Memory32 queries](../../Silmaril/Wasm/Institution/Operational/MemoryQuery/Native/Thms.lean) and [writes](../../Silmaril/Wasm/Institution/Operational/MemoryWrite/Native/Thms.lean) | Isolated `memory.size`, full-width `i32.load`, and full-width `i32.store` at index zero and static offset zero. The bounds trap preserves the store. | Packed and floating accesses, other offsets, Lime1 bulk operations, and Core memory64 or multiple memories. |
| [Memory32 growth](../../Silmaril/Wasm/Institution/Operational/MemoryGrow/Native/Thms.lean) | An isolated `memory.grow` at index zero. The Core spec profile agrees on aligned buffers and representable maxima. Success appends zero-filled pages and returns the old size. Failure returns all ones and preserves the store. | Oracle-controlled growth, multiple memories, and memory64. |
| [Direct-call resolution](../../Silmaril/Wasm/Institution/Operational/CallResolution/Native/Thms.lean) and [typed callee frames](../../Silmaril/Wasm/Institution/Operational/CallFrame/Native/Thms.lean) | Individually checked resolution and resolved invocation of one allocated non-host function. Numeric locals, at most one result, explicit return, fallthrough, and trap propagation. The typed caller keeps its value prefix. | Indirect calls, host contracts and divergence, and composition with caller continuations. |
| [Checked indirect-call resolution](../../Silmaril/Wasm/Institution/Operational/CallResolution/Indirect/Native/Thms.lean) | Core and Lime1 read a fixed allocated Table32 at module slot zero. Exact successors consume the unsigned i32 selector while retaining the numeric operands and pending continuation. Bounds, null, and signature mismatch have separate checked outcomes. Successful lookup enters the allocated graph function on its ordered numeric argument suffix. | The separate contextual theorem below applies after successful resolution. Other table profiles, host targets, and V1 remain open. |
| [Indirect-call contextual readback](../../Silmaril/Wasm/Institution/Operational/CallResolution/Indirect/Context/Thms.lean) | A successfully resolved Table32 site enters a checked, allocated Core or Lime1 graph callee. Exact native prefixes include four Core steps or two Lime1 steps through frame entry, arbitrary finite prefixes of cyclic direct calls, ordered return above the saved caller operands, and trap discard up to the bare caller trap. | Execution of the resumed caller instructions, indirect calls in graph bodies, mutable tables or stores, host calls, and V1. |
| [Saved caller continuation](../../Silmaril/Wasm/Institution/Operational/CallContinuation/Native/Thms.lean) | One pending `nop` stays in the caller during a resolved invocation. Return reinstates the caller's value prefix and scalar result before `nop` executes. Trap steps discard the continuation and may discard saved values in several steps. | General instruction suffixes and caller-side state changes. |
| [One nested non-host call](../../Silmaril/Wasm/Institution/Operational/CallContinuation/Nested/Native/Thms.lean) | Start with an already-entered outer frame and label around one allocated, resolved inner call. The inner return runs the outer `nop`, exits the label, and returns across the outer frame when the stack has its declared arity. An inner trap discards the pending instruction and propagates through both outer boundaries. | General instruction suffixes or effects, outer source typing, and arbitrary depths or recursion. |
| [Typed outer invocation](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/Native/Thms.lean) | Starts at an ordinary direct `call`. The outer function receives its numeric arguments and default locals, supplies literal arguments to one distinct allocated non-host inner callee, and resumes at one `nop`. Exact successors and finite endpoints include both returned values and a propagated trap. | General continuations, general argument expressions, host calls, indirect calls, recursion, extra top-level stack operands, and whole-module validation. |
| [Computed inner argument](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/Computed/Native/Thms.lean) | Two typed reads from the entered outer frame and one same-width integer binary operation produce one inner argument. The public configuration maps preserve every phase. A numeric trap can discard the pending call with or without its following `nop` in the same step and leaves the outer frame without entering the inner callee. | General argument operations, arbitrary continuations, host and indirect calls, recursion, and whole-module validation. |
| [Composable argument prefixes](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/Computed/Sequence/Native/Thms.lean) | A finite prefix of typed local reads and integer binary operations computes the full inner argument stack. The [prefix correspondence](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/Computed/Prefix/Native/Thms.lean) is independent of the pending instructions. The call guard keeps one distinct allocated non-host callee and one pending `nop`. Exact successor and finite endpoint readback include early traps that discard part or all of the saved operand and instruction context. | Other prefix operations, caller-side local writes and effects, general continuations, host and indirect calls, recursion, and whole-module validation. |
| [Typed straight-line caller continuation](../../Silmaril/Wasm/Institution/Operational/CallContinuation/StraightLine/Native/Thms.lean) | A direct inner call inside an entered outer frame and label saves a checked sequence of local reads and integer binary operations. The check starts at the exact saved operands and returned values. The callee trap bypasses every continuation operation, including when intermediate trap steps discard only part of the saved operands or instructions. Exact successors and finite endpoints preserve the store and caller frame across V1, Lime1, and Core. | Caller-side state changes, unrestricted control flow, recursion, and host calls. |
| [Outer call with computed arguments and continuation](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/Computed/Sequence/Composed/Native/Thms.lean) | An ordinary typed outer call computes the inner arguments, invokes a distinct allocated non-host callee, and resumes a checked local-read and integer-binary continuation. The callee source guard admits reads and constants, explicit return, or unreachable. Exact step and finite endpoint readback include normal return, argument traps before inner entry, callee traps that skip the continuation, and traps during continuation evaluation. | State updates, arbitrary control flow, host or indirect calls, recursion, and whole-module validation. |
| [Finite straight-line direct calls](../../Silmaril/Wasm/Institution/Operational/CallContinuation/StraightLine/Sequence/Native/Thms.lean) | In a fixed, already-entered caller frame, a checked list interleaves local reads, integer binary operations, and direct calls to a finite table of allocated read-only non-host callees. A return restores the saved operand prefix and puts the callee's result on top for the remaining code. A trap may discard operands and instructions in stages, and pending calls are bypassed. Exact step and finite endpoint readback identify the full store, frame, and code in V1, Lime1, and Core. | Entry to and exit from the enclosing caller, state updates, unrestricted control flow, recursive and indirect calls, host calls, and whole-module validation. |
| [Outer invocation with finite straight-line calls](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/DirectSequence/Native/Thms.lean) | An ordinary direct call starts with the exact numeric arguments. It initializes default numeric locals, executes any checked finite list from the previous row, and leaves its label and frame with the declared optional numeric result or a propagated trap. Exact successor and finite endpoint readback preserve the store and restore the enclosing frame in all three versions. A trap can discard pending operations in stages before either enclosing boundary exits. | Operands below the outer arguments and instructions after the outer call, multiple results, additional outer source operations or exits (including explicit `return`), nested or recursive target calls, indirect and host calls, state updates, arbitrary control flow, and whole-module validation. |
| [Finite outer call in a checked enclosing continuation](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/DirectSequence/Enclosing/Native/Thms.lean) | A fixed, already-entered enclosing frame supplies saved numeric operands and a finite sequence of local reads, integer binary operations, and direct calls. The continuation has its own table of typed, read-only non-host targets. Its function indices must resolve in the enclosing frame and its declarations must match the allocated functions. The outer call preserves both saved contexts and places its exact optional result above the prefix at resumption. An outer trap bypasses the whole continuation, with exact readback for partial operand and instruction discards. | Additional enclosing labels and frame exits, outer and target signatures with multiple results, nested calls in continuation target bodies, recursion, indirect and host calls, state updates, unrestricted control flow, other instructions in the continuation, and whole-module validation. |
| [Enclosing function label and frame exits](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/DirectSequence/Enclosing/Framed/Native/Thms.lean) | The previous row executes under one already-entered function label and frame with a declared numeric result stack. Exact successor and finite endpoint readback carry the ordered values or a fully unwound trap through both exits and restore the distinct calling frame. The label-exit test is shared with direct-sequence invocation and works for any checked straight-line sequence under an empty label continuation. | Source entry for the additional enclosing function, saved operands and instructions in its caller, ranked call-graph declarations and arbitrary nesting, multiple-result source invocation, recursion, indirect and host calls, state updates, unrestricted control flow, and whole-module validation. |
| [Typed source entry and return for the enclosing function](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/DirectSequence/Enclosing/Framed/Source/Native/Thms.lean) | An ordinary direct call with exact numeric arguments resolves to a checked, allocated non-host body. Entry initializes default locals. The source body supplies literal operands for the checked invocation and resumes its finite continuation. The shared [call descriptor](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/Declaration/Defs.lean) keeps the declaration and resolved address independent of the actual arguments. Exact native successor and finite endpoint readback extend through restored-caller return and trap. V1 admits zero or one result. Lime1 and Core admit the declared ordered numeric result stack. | Saved operands and instructions outside this new function, ranked nesting beyond the fragment below, arbitrary source argument expressions in the new body, recursion, indirect and host calls, state updates, unrestricted control flow, and whole-module validation. |
| [Rank-decreasing direct targets](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/Ranked/Native/Thms.lean) | A finite address-indexed table checks module index resolution, declaration agreement, and strict rank decrease on every registered edge. The body check matches the complete target lists of the entered source function, its inner direct-call sequence, and their flat callees. Native guards supply allocation, body typing, and the V1 zero-or-one-result restriction. Every read-back endpoint in Core, V1, and Lime1 has a chain of resolved, descending entered frames. Fixtures pass through three simultaneous frames before returning to the original caller or unwinding to a trap. Core and Lime1 retain ordered numeric result lists. | The whole-graph readback below covers arbitrary depth in a straight-line fragment. Recursion, indirect and host calls, unrestricted control flow, state updates, and whole-module validation remain open. |

## Rank-recursive direct-call judgment

The [ranked graph judgment](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/Ranked/Graph/Thms.lean)
interprets one typed activation at a time by well-founded recursion on resolved
targets. The graph checker derives the target table from each body and checks
the typed operand prefix, local reads and writes, integer binary operations,
direct calls, scalar structured labels, indexed blocks, conditionals, and loops
in Core and Lime1, unconditional and conditional branch exits, explicit return,
and normal fallthrough. The judgment also covers unreachable and partial trap
discards. Exact active-call inversion identifies the child's step and the
caller's unchanged continuation. Finite runs preserve typing and the
descending chain of entered frames. The four-frame fixtures cover return and
propagated trap. The V1 checker enforces zero or one function result and
unindexed syntax throughout every declared body.

The [native graph theorems](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/Ranked/Graph/Native/Thms.lean)
bind each declared function to its allocated store instance and resolve the root
call in its enclosing caller. Exact successor and finite endpoint readback hold
for Core, Lime1, and V1 through arbitrary finite nesting. The proof reuses the
entered-child context lemmas and descends along each resolved target. V1 child
reflection uses the graph-wide source and result-arity guard and preserves
unindexed syntax at each intermediate phase. Core and Lime1
retain the declared mixed-width result order. The native fixtures pass through four
simultaneous frames before returning to the original caller or propagating a trap,
including separate discards of pending code and saved operands.

The graph composes the existing [numeric local SOS](../../Silmaril/Wasm/Institution/Operational/Locals/Native/Thms.lean)
with ranked calls. Each entered frame carries its current numeric locals,
initialized from arguments and default locals. The checker validates the
slot type for both writes. `local.set` consumes its operand. `local.tee` duplicates the operand and schedules a
set, leaving the write visible as a separate native successor. On return, the
caller resumes with its saved locals and operands. On a trap, pending writes
are discarded as the frames unwind. Regressions check modified child values,
isolation of both local vectors, and caller restoration in all three dialects.

An explicit function-body `return` checks that the top operands match the declared
result types and arity. Its label step discards pending callee instructions. Its
frame step discards operands below the results and restores the suspended caller's
locals, operand prefix, and continuation. Core and Lime1 preserve mixed-width
result order. V1 retains the graph-wide zero-or-one-result guard. The nested
regressions check both exits, an observable resumed continuation, and a trap in
the same caller context. Stack checking ends at `return`. The table still checks
every declared call target in the body. See the public reduction rules for
[Wasm 1.0](../../specs/spectec/src/specification/wasm-1.0/8-reduction.spectec#L135)
and [Wasm 3.0](../../specs/spectec/src/specification/wasm-3.0/4.3-execution.instructions.spectec#L230).

The [structured label context](../../Silmaril/Wasm/Institution/Operational/Blocks/Context/Thms.lean)
supplies exact contextual step inversion for a block with saved operands and
pending instructions. An entered ranked callee can step inside the block while
retaining that context. Normal fallthrough and an already-reduced trap leave the
label and deliver their respective outcomes. An independent SOS crosses one
label per explicit-return step and gives exact finite endpoint readback in Core,
Lime1, and V1. The return guard checks the enclosing function's result types.
Each label preserves the return operands in order and discards its remaining
body. The existing frame exit selects the function's result suffix. Fixtures
enter two scalar source blocks, traverse both labels, and return through the
function frame with the ordered results.

The ranked source checker now checks blocks recursively from an empty operand
stack and includes their direct calls in the rank table. Each block declares
zero or one numeric fallthrough result. The enclosing function's return types
remain in scope beneath every block. A suspended block retains its caller's
operand prefix and pending code. A nested callee can return to the block,
which continues with the same locals and the callee's result. Block fallthrough
appends the block's result to the saved operands. Explicit return crosses each
label, dropping its pending code, before the function frame selects the result
suffix. Traps can discard pending code and operands in stages before leaving
each label. The graph's exact native successor and finite endpoint theorems cover
all these stages in Core, Lime1, and V1 under the existing allocation, rank,
and dialect guards.

The ranked checker also admits scalar `if`/`else` with an `i32` condition.
It checks both arms against the same optional fallthrough type, carries the
enclosing function's return types into each, and includes direct calls from
both arms in the rank table. The selection step consumes the condition and
leaves a source block for the chosen arm with the saved operands and pending
code intact. The block rules then handle entry, calls, fallthrough, return, and
trap propagation. Exact native successor and finite endpoint readback cover
selection and all subsequent steps in Core, Lime1, and V1. Fixtures exercise
both arms, a ranked child call, explicit return through nested labels, and a
child trap that bypasses the saved continuation.

The ranked checker also checks unconditional `br` to its block and conditional
labels. It resolves the depth through the label stack and checks the result
annotation and operand suffix against that target. The target's types are
independent of the current label's fallthrough and the function's return
types. Each positive-depth step drops the crossed label's pending instructions
and lowers the index. The target exit keeps exactly the ordered result suffix
and resumes the target's saved operands and code. Core, Lime1, and V1 have exact
successor and finite endpoint readback at each stage. Fixtures cover depth zero
and a branch from an inner block to the surrounding conditional, with an
observable noncommutative continuation. They reject missing or mistyped
operands, an incorrect target annotation, and an out-of-range depth.

The same label guard checks `br_if`. It verifies the target and its operand
suffix after an `i32` condition is popped and checks fallthrough with those
operands still on the stack. For a nonzero condition, the first SOS step
leaves an ordinary branch for the existing label propagation rules. A zero
condition advances directly to the pending instructions. Exact native
successor and finite endpoint readback cover both paths in Core, Lime1, and
V1. The nested fixtures distinguish results and continuations on both paths
and reject bad types and targets even with a default-zero condition.

Ranked `br_table` checks every listed depth and the default against the same
optional numeric result and the operand suffix under an `i32` selector. The
selector is interpreted as unsigned. A zero-based in-range slot supplies its
depth, and any index at or beyond the length uses the default. An empty table
always uses the default. The selection step keeps the operands and pending
code and leaves an ordinary `br` for the checked label rules. Core, Lime1, and
V1 have exact native successor and finite endpoint readback. Fixtures cover
indexed and default targets, the all-ones selector, empty tables, and invalid
unselected targets.

The same branch checker and rules cover the implicit function label. Each
call starts a fresh label scope with the function's declared result list.
Blocks and conditionals add their own scalar result types as inner labels.
A branch to the function label keeps the ordered result suffix, drops its
pending instructions, and leaves the callee frame holding those results.
A separate frame step returns the values to the saved caller. Exact native
successor and finite endpoint readback cover both steps in Core, Lime1,
and V1. Core and Lime1 admit mixed-width result lists. V1's graph-wide
zero-or-one-result guard still applies. Fixtures cover direct function
branches, conditional and table branches crossing a block, resumption of
a caller, and rejection of a depth that would reach the caller's labels.

[Native scalar loop inversion](../../Silmaril/Wasm/Institution/Operational/Loops/Native/Thms.lean)
covers unindexed zero-parameter entry, depth-zero restart, and value/trap
exit in Core, Lime1, and V1. Entry saves the outside operands and code.
The label's branch arity is zero even with a scalar fallthrough result.
A depth-zero branch drops the iteration's operands and pending instructions,
then reinstates the original loop instruction for a separate entry step.
Value fallthrough and trap exit skip that restart continuation. See the
[Wasm 1.0 reduction rules](../../specs/spectec/src/specification/wasm-1.0/8-reduction.spectec#L67)
and [Wasm 3.0 loop entry](../../specs/spectec/src/specification/wasm-3.0/4.3-execution.instructions.spectec#L80).
[Native fixtures](../../tests/wasm/scalar-loop-native/Regression.lean)
check that exactly two configurations are reachable by finite prefixes of a typed self-loop
and a scalar loop that restarts once, then resumes its saved continuation.
For unindexed loops, the ranked checker admits no parameters and zero or one numeric
fallthrough result. It checks the body recursively with an empty operand stack
and an empty branch payload for the loop label. The declared fallthrough
result and enclosing function result types are checked separately. Calls in
a loop body still contribute to the allocated, rank-decreasing target table.

A scalar-loop restart discards iteration operands and pending code, retains the current
locals and saved outer context, and reinstates the original loop instruction.
The same checked entry rule then starts the next iteration. Fallthrough,
branches crossing the loop, explicit return, and trap continue through the
existing label and frame rules. Core, Lime1, and V1 have exact successor and
finite endpoint readback under the existing allocation and arity guards.
Finite trace induction covers repeated back-edges, with call rank used for
descent into callees. Ranked regressions cover a local update surviving
restart, a caller consuming the returned scalar with a saved operand, exact
finite prefixes of a scalar-result self-loop, and malformed branch and
fallthrough checks.

The ranked checker resolves an indexed block against the exact type table of
the allocated function's module. Lime1 indexes function signatures directly.
Core expands the corresponding translated defined type to the same numeric
parameter and result lists. Entry moves the ordered parameter suffix into the
new label and saves the stack below it. The body is checked against the block
results for fallthrough and branches to that label, while explicit return
retains the enclosing function's result types. Block exit puts the ordered
result suffix above the saved stack. Exact Core and Lime1 successor and finite
endpoint readback reuse the native indexed-entry inversion and the ranked
label rules. The called-block fixture checks mixed-width argument and result
order, callee-local writes, and caller stack and local restoration. See the
[Core block entry rule](../../specs/spectec/src/specification/wasm-3.0/4.3-execution.instructions.spectec#L77)
and the [Wasm 1.0 block rule](../../specs/spectec/src/specification/wasm-1.0/8-reduction.spectec#L63).

An indexed conditional uses that same type-table lookup. Both arms are checked
with the declared parameter and result stacks, including the arm skipped at
runtime. Selection consumes the i32 above the parameters and leaves the operands
and continuation intact. The next step enters a block with the same index and
the selected body. The Core and Lime1 regressions exercise nonzero selection
with normal fallthrough and zero selection with `br 0`, both returning ordered
mixed-width results to a suspended caller. See the [Core conditional rule](../../specs/spectec/src/specification/wasm-3.0/4.3-execution.instructions.spectec#L85)
and the [Wasm 2.0 conditional rule](../../specs/spectec/src/specification/wasm-2.0/8-reduction.spectec#L76).

Indexed loop entry uses the same exact module lookup. The body starts with the
ordered parameter suffix. A branch to the loop label delivers that same type
list as its restart operands, while fallthrough uses the declared loop results
and `return` uses the enclosing function result types. The back edge discards
pending iteration code and extra iteration operands. It places the ordered
restart operands above the saved prefix with the indexed loop instruction
pending. A separate entry step consumes that suffix into the next iteration,
using the updated locals. Core and Lime1 have exact native successors and
finite endpoint readback even when a loop can keep restarting. The ranked
fixtures check a mixed-width restart and re-entry, fallthrough with a different
arity and a preserved prefix, explicit return, and malformed type or operand
guards.

V1 rejects indexed syntax even after unconditional exits and in unselected
arms. Its native readback theorems take an explicit syntax premise on the
starting phase, which permits applying them to intermediate configurations.

## Checked recursive direct calls

The Core and Lime1 frame judgments use the same typed bodies and exact
allocated declarations as the ranked graph. The direct-call checker still
checks that each source index resolves to its declared allocated target and
that the target agrees with the callee's declaration. It accepts self-edges and
other correctly linked cycles. The original ranked checker requires strict
descent on every registered edge, and the new frame judgment is equivalent to
the ranked judgment on that domain. V1 continues to use the ranked checker.

The single-step proof descends through the active child of the finite source
configuration. Entering a call can increase the number of frames. Exact
successor and finite endpoint readback therefore apply without a bound on call
depth or a termination premise. There is no execution fuel or corresponding
trap case. The fixed-function regressions cover a base-case return to saved
caller operands and locals, a propagated `unreachable` trap that bypasses the
continuation, and reachable prefixes at every finite depth for a function that
always calls itself. The generic theorem uses exact allocation and typing for
every function in the admitted graph. Indirect calls inside graph bodies, host calls, mutable stores,
whole-module validation, and infinite-run correspondence are separate.
[Native graph theorems](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/Ranked/Graph/Native/Thms.lean)

Lime1 resolves the indirect call in one native step. Core unfolds it into
`table.get`, a nullable cast, and `call_ref`. The exact resolution trace ends at
the pending call or the first trap, with the rest of the lowered instructions
still present when applicable. An out-of-bounds index traps before the cast.
A null reference passes the nullable cast and traps at `call_ref`. A nonnull
entry of the wrong signature fails the cast. On these translated numeric
function types, Core subtyping at the cast agrees with Lime1 signature equality.
Missing type indices or target declarations fail the site guard.
[Wasm 3.0 reduction rules](../../specs/spectec/src/specification/wasm-3.0/4.3-execution.instructions.spectec#L220)
and [Wasm 2.0 reduction rules](../../specs/spectec/src/specification/wasm-2.0/8-reduction.spectec#L122).

Successful resolution gives the typed graph invocation edge and exact native
frame entry without requiring a direct function index in the caller. Core has
four steps through entry. Lime1 has two. Inside the entered frame, the checked
cyclic graph's direct-call relation reads back each native successor and every
finite prefix, with no recursion-depth or termination assumption.

The contextual run stops on successful handoff with the caller frame and locals
restored, the ordered results above its saved operands, and the pending
instructions still in place. On trap, the native discard rules can drop saved
operands and pending instructions in one or more steps, bypassing the
continuation. The readback covers all such intermediate trap contexts and the
bare caller trap. The fixtures use a mixed-width return, an observable caller
continuation, a callee trap, and prefixes at arbitrary depth in a self-recursive
callee. The site itself must resolve successfully. The resolution-only
theorems cover failed lookups separately. The graph checker still admits only
direct calls inside its bodies.
[Contextual readback](../../Silmaril/Wasm/Institution/Operational/CallResolution/Indirect/Context/Thms.lean)

The shared legacy baseline uses the native public Wasm V1 and Lime1 relations.
Lime1-specific multi-value and bulk-memory cases and newer Core features have
separate obligations. Whole-module validity and execution, initialization, host
interaction, divergence, and maximal observations require further correspondence.
See the [native version injections](wasm-version-injections.md) and the
[SpecTec snapshot manifest](../../specs/spectec/manifest.json).
