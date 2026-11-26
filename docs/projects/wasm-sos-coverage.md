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
| [Memory32 queries](../../Silmaril/Wasm/Institution/Operational/MemoryQuery/Native/Thms.lean) and [writes](../../Silmaril/Wasm/Institution/Operational/MemoryWrite/Native/Thms.lean) | Isolated `memory.size`, full-width `i32.load`, and full-width `i32.store` at allocated module slot zero. Accesses use an unsigned 32-bit immediate and compute the effective address as a natural sum. Unaligned ranges can succeed. An out-of-bounds range traps with the exact original store and frame. | Packed and floating accesses, Core memory64 and immediates outside the legacy 32-bit range, other memory slots, Lime1 bulk operations, and composition in general code. |
| [V1 Memory32 under a function frame](../../Silmaril/Wasm/Institution/Operational/MemoryWrite/Native/Thms.lean) | Exact readback for a leading full-width offset load or store in a current frame or an entered scalar function label and frame. Slot zero resolves in the active module. Both continuations survive the access step and a second frame resolving the same memory sees the updated bytes. Fixtures follow a normal call through the caller's read and a bounds trap through native discard with an earlier write retained. | Memory operations as typed ranked graph operators, shared-store invariants across arbitrary graph traces, and structured control around the access. |
| [Ranked V1 Memory32 typing and store preservation](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/Ranked/Graph/Memory32/Thms.lean) | The V1 checker reuses ranked call resolution and checks the i32 operands of full-width offset loads and stores. Parameterless blocks check their bodies from an empty operand stack against a void or scalar result. A scalar `if` consumes an i32 and checks both arms against the same optional result. Each continuation receives that result above the saved operands. Explicit returns use the enclosing function result types. Every activation maps slot zero to the same allocated memory. Updates preserve its extent, function allocation and other store entries. | Branches, loops, and the opt-in growth profile are covered below. Recursive or host calls and multiple mutable memories remain separate. |
| [Ranked V1 Memory32 native execution](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/Ranked/Graph/Memory32/Run/Thms.lean) | Exact successors and arbitrary finite endpoints for the checked fragment, including nested blocks, scalar conditionals, and parameterless loops. One live byte array is shared by all activations. V1 first selects an arm as a block, then opens its label. Selection preserves the frame, store, saved operands and continuation. The unchosen arm has no effects. Regressions stop at intermediate label entry, observe a callee write after normal arm exit and after nested void and scalar block completion, and preserve an earlier write through separate label and frame discards after a bounds trap. [Wasm 1.0 block and conditional steps](../../specs/spectec/src/specification/wasm-1.0/8-reduction.spectec#L60) | Broader source control, recursion, other memory profiles, whole-module validation, and infinite execution correspondence. |
| [Ranked V1 Memory32 branch exits](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/Ranked/Graph/Memory32/Thms.lean) | Checked `br` and `br_if` resolve among enclosing blocks, if arms, and the current activation’s implicit function label. Depth and target signatures are checked throughout the body, and reachable `br_if` checks its payload even for a zero condition. Native readback preserves the saved operands and reflects selection, depth lowering, and target delivery as separate steps. Tests start from ordinary entry and retain a callee write on the taken path. On fallthrough the condition is consumed and the preserved operands are used by a subsequent store. A separate depth-two exit to the function label keeps the prior write, skips the pending function tail, and delivers the declared result inside the frame before a separate frame completion. [Wasm 1.0 branch steps](../../specs/spectec/src/specification/wasm-1.0/8-reduction.spectec#L78) | Loop backedges and table selection are covered below. |
| [Ranked V1 Memory32 loops](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/Ranked/Graph/Memory32/Run/Thms.lean) | Parameterless scalar or void loops validate an empty `br` or `br_if` payload at the loop label, independently of the declared fallthrough result. A taken backedge restores the loop instruction, then a separate step re-enters the body with the current locals, saved operands, and live memory. Exact readback covers arbitrary finite prefixes. The fixture reaches a write, restarts with the updated bytes and locals, then falls through on a zero condition and delivers its scalar result. [Wasm 1.0 loop and branch steps](../../specs/spectec/src/specification/wasm-1.0/8-reduction.spectec#L66) | Indexed types, recursion, and host calls. |
| [Ranked V1 Memory32 branch tables](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/Ranked/Graph/Memory32/Run/Thms.lean) | The checker requires an i32 selector, one operand suffix, and the same signature at every listed target and the default. Target checks also cover skipped code. Native selection uses the unsigned selector as an index and emits an ordinary branch, with depth lowering and delivery reflected as later steps. A fixture preserves a callee's write through indexed if-arm, loop, and block targets and an out-of-range default to the implicit function label. [Wasm 1.0 table branch steps](../../specs/spectec/src/specification/wasm-1.0/8-reduction.spectec#L101) | Indexed signatures, recursive or host calls, and whole-module validation. |
| [Isolated Memory32 growth](../../Silmaril/Wasm/Institution/Operational/MemoryGrow/Native/Thms.lean) | Exact V1 `memory.size` reads the selected instance. For `memory.grow`, alignment, the Memory32 page cap, and the declared maximum govern success. Success returns the old count and appends zero-filled pages. The native rule also permits resource failure within the limits. Failure returns all ones and preserves the entire store and frame. The Core spec profile agrees on aligned buffers and representable maxima. [Wasm 1.0 size and growth rules](../../specs/spectec/src/specification/wasm-1.0/8-reduction.spectec#L265) | Oracle-controlled growth, multiple memories, and memory64. |
| [V1 Memory32 extent-changing store boundary](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/Ranked/Graph/Memory32/Thms.lean) | A single live byte array retains the selected allocation and declared limit. Growth preserves alignment, the page bounds, and monotonic extent. Stores preserve the current extent. A native fixture grows one page, compares old and new counts, and uses the grown allocation in a ranked call that reads a zero word in the new page. | Growth inside ranked bodies is covered below. |
| [Ranked V1 Memory32 size and growth](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/Ranked/Graph/Memory32/Run/Thms.lean) | The growth profile checks an aligned initial allocation and binds its declared maximum. Its single live byte array remains aligned, bounded, and monotone across exact native successors and arbitrary finite runs. Both native outcomes are reflected for an in-limit request, and only failure is possible beyond the limits. A suspended caller reads the increased size and a zero word in the appended page. The failure prefixes retain the old bytes and page count. The fixed-extent profile keeps its existing correspondence. | Multiple mutable memories, memory64, host calls, and whole-module validation. |
| [Checked recursive V1 direct calls with shared Memory32](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/Ranked/Graph/Memory32/Run/Thms.lean) | The opt-in recursive checker resolves every direct target in its caller module and checks its exact declaration in a finite allocated function graph. The same V1 successor and finite-run correspondence applies without rank descent, using induction on the finite step under entered contexts and then on the finite trace. Entry preserves the live store and suspended caller, and normal return closes the function label before delivering results above the saved caller operands. A self-call fixture reads back its second activation and resumption, then observes the recursive callee’s nonzero-offset write from the caller. The fixed and growth profiles each retain one shared slot, and the growth fixture reflects both in-limit outcomes under either call policy. [Wasm 1.0 invocation and frame rules](../../specs/spectec/src/specification/wasm-1.0/8-reduction.spectec) | Infinite-run correspondence, indirect and host calls, indexed or multiple-result signatures, multiple mutable memories, and whole-module validation. |
| [Direct-call resolution](../../Silmaril/Wasm/Institution/Operational/CallResolution/Native/Thms.lean) and [typed callee frames](../../Silmaril/Wasm/Institution/Operational/CallFrame/Native/Thms.lean) | Individually checked resolution and resolved invocation of one allocated non-host function. Numeric locals, at most one result, explicit return, fallthrough, and trap propagation. The typed caller keeps its value prefix. | Indirect calls, host contracts and divergence, and composition with caller continuations. |
| [One checked direct V1 host call](../../Silmaril/Wasm/Institution/Operational/HostCall/V1/Thms.lean) | An ordinary direct call resolves one allocated host identifier and its declared numeric signature. The ordered arguments are the suffix above the saved operands. Exact native steps reflect each declared return, trap, or divergence self-step. The embedding proves the exact result types and a caller-selected store relation for every returning outcome, including traps. Delivery preserves the caller frame, operand prefix, continuation, and the actual returned store. A shared-Memory32 fixture observes two distinct returned byte arrays from the same arguments and retains the returned bytes on a trap while discarding the caller tail. | Host instructions in checked graph bodies, host calls under general source contexts, embedding validation, later-version results, and infinite execution observations. The finite theorem leaves the caller's post-delivery run native. |
| [V1 host-return store and linkage for the Memory32 graph](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/Ranked/Graph/Memory32/Run/Host/Thms.lean) | Every returned outcome, including a trap, needs proof that the effect is an update to the selected live allocation. The graph recovers the exact returned bytes, checks the extent against the pre-call extent, and reconstructs its native function and fixed-table layout. A typed host result with an already admitted caller tail yields a ready graph configuration. Fixtures resume the same caller after distinct native store outcomes, read the host-written bytes, and reflect enclosing label and frame cleanup after a trap. Divergence is a pending self-step. A host with no outcome offers no delivery step. | The computed direct-site theorem below composes this store boundary with dynamic argument typing and finite continuation readback. |
| [Computed direct V1 host site with a checked Memory32 continuation](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/Ranked/Graph/Memory32/Run/Host/Body/Thms.lean) | A typed numeric prefix carries the active declaration's local types and a checked graph tail. Each successful numeric step preserves that invariant. At the reached call, it yields the ordered parameter suffix above the saved stack, with separate evidence for the current module index, allocated host, and scalar signature. Exact pending successors beneath entered native labels and frames reflect every declared return or trap with its store, or a divergence self-step. An invocation with no outcome has no successor. Under the embedding's result and store contract and the enclosing graph guard, arbitrary finite runs read back the delivered result and the checked host-free continuation, including memory reads and enclosing trap cleanup. | This theorem starts under an entered context. The designated source entry below derives that context from ordinary invocation. |
| [Ordinary V1 entry to one checked direct host site](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/Ranked/Graph/Memory32/Run/Host/Entry/Thms.lean) | The opt-in entry guard links the ordinary source call to its actual allocated Wasm function, checks the numeric prefix and graph tail, and links the designated host within the active module. Native resolution, initialized locals, and frame and label entry precede the prefix. Every checked prefix reaches a typed pending invocation or an earlier numeric trap. Exact successors and finite runs reflect host return and trap with their returned store, declared divergence, and a pending invocation with no enabled host outcome. The embedding proves result typing and the live-memory update for every returned outcome. After delivery, the existing shared-Memory32 graph handles the tail and native unwind. A fixture starts at the ordinary call, reads returned bytes and invokes a guarded non-host callee in the resumed tail. | One entry function with literal operands and a numeric prefix leading to a direct host call under its function label. The sequence theorem below allows later direct sites. |
| [Straight-line sequences of direct V1 host sites](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/Ranked/Graph/Memory32/Run/Host/Sequence/Thms.lean) | The checked entry verifies a finite list of numeric prefixes and direct sites in the actual allocated body. Each pending invocation carries its ordered argument suffix, the saved operands, the checked later sites and the live memory extent. For every declared return the embedding proves result typing and the selected-memory update from that invocation's current store. A value result resumes the remaining source with the new bytes, and a trap keeps the returned bytes while discarding the remaining sites in native order. Exact successors and finite endpoint readback distinguish return, declared divergence and absence of an outcome. The fixture uses two first outcomes that give the same later site different arguments and stores, and a first trap that skips it. | The numeric prefixes between sites use local reads and integer binary operations under the function label. The final host-free tail uses the existing graph profiles. The structured entry profile below adds block and conditional regions. |
| [Checked scalar control with V1 direct hosts in arms and enclosing tails](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/Ranked/Graph/Memory32/Run/Host/Sequence/Thms.lean) | Ordinary entry derives the active frame for recursively checked parameterless blocks and conditionals. Both arms and enclosing source tails are checked, including all declared host links. Native i32 selection runs only the selected arm. On normal label exit, the ordered result is placed above the saved operands, and the resumed source tail sees the live Memory32 returned by the child. On a trap, native steps discard affected labels and their tails while retaining the returned store. Exact successors distinguish each contracted return, a declared divergence self-step, and a pending invocation with no outcome. Finite readback covers arbitrary endpoints from ordinary entry. Regressions include different hosts in both conditional arms and a mixed-width enclosing host invocation that consumes a child result and sees changed bytes, as well as trap cleanup that skips that invocation. | A live host-enabled enclosing tail requires the child to reach a checked value-only boundary. Arbitrary host-free graph suffixes remain supported when no enclosing source tail must resume. General branch and loop dispatch to hosts, indirect hosts, whole-module validation and infinite runs remain separate. |
| [Checked forward branches between V1 host regions](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/Ranked/Graph/Memory32/Run/Host/Sequence/Thms.lean) | A source region or its checked direct host sequence can end in a statically typed unconditional `br` to an explicit scalar or void block or conditional label. The checker uses that label's result signature and the ordered branch suffix, with the implicit function label excluded. Each native step across a label lowers the depth by one and exposes the next enclosing tail in the code. At depth zero the branch discards that tail and delivers the typed suffix above the target's saved operands. Exact successor and arbitrary finite readback from ordinary entry pass the live Memory32 through the transfer. The regression crosses an inner label after a host write, checks the skipped host's instruction in the intermediate native prefix, and reaches a different host with the retained bytes and a mixed-width stack. Rejections cover the implicit label, an out-of-range depth and a wrong payload type. | The source branch is terminal in its region. Loop back-edges, indirect hosts, whole-module validation and infinite runs remain separate. |
| [Checked `br_if` between V1 host regions](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/Ranked/Graph/Memory32/Run/Host/Sequence/Thms.lean) | The checker validates an i32 test above the ordered branch suffix, an explicit scalar or void target, and the fallthrough source on the remaining operands. A checked direct host sequence can continue to this test with its returned store. The native zero step consumes just the test and runs the checked fallthrough. The nonzero step consumes the test and retains the fallthrough in the lowered `br` configuration until the native label transfer discards it. Both paths retain live Memory32. Exact successors and arbitrary finite readback start at ordinary entry under the existing embedding contract. The two-path fixture observes different operands and bytes at the final host depending on whether the intervening host ran. Static controls reject bad depths, invalid tests or payloads, and an ill-typed fallthrough. | Explicit scalar or void block and conditional targets. Loop back-edges, indirect hosts, whole-module validation and infinite runs remain separate. |
| [Checked `br_table` between V1 host regions](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/Ranked/Graph/Memory32/Run/Host/Sequence/Thms.lean) | A terminal source table checks the i32 selector and the common ordered payload against every listed depth and the default. The native step consumes the selector, uses its unsigned value as a zero-based index, and lowers to the existing checked branch. Both indexed and default paths preserve live Memory32 and the target's saved operands through exact native label steps. Finite readback starts at ordinary function entry under the host embedding contract. The fixture reaches distinct labels, observes skipped host code in the intermediate prefix, and checks the delivered payload and store at each reached host. Static controls cover the empty vector and reject an invalid default, an invalid unselected entry, or a listed void label alongside scalar targets. | Explicit scalar or void block and conditional targets. Loop back-edges, indirect hosts, whole-module validation and infinite runs remain separate. |
| [Checked function-label branches in V1 host regions](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/Ranked/Graph/Memory32/Run/Host/Sequence/Thms.lean) | `br`, taken `br_if` and `br_table` share the checked transfer to the implicit function label below all explicit labels. The checker uses the function's declared scalar or void result signature. Each crossed explicit label lowers the depth by one. At the function label, the native branch discards the remaining instruction suffix and scratch operands, leaving the ordered result alone inside the active frame. Native frame completion is a separate step that delivers those values to the caller. Exact successor and finite-prefix readback from ordinary entry retain the live host-updated Memory32 in both steps. Fixtures cover nested transfers for all three instructions, a table default, the zero conditional path reaching its host, and rejection of malformed depth or incompatible function results. | Indirect hosts, whole-module validation and infinite traces remain separate. |
| [Checked void loops in V1 host regions](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/Ranked/Graph/Memory32/Run/Host/Sequence/Thms.lean) | An unindexed parameterless void loop holds its checked restart body alongside the saved outer operands and normal continuation. A taken `br_if` lowers to a branch, and the depth-zero native branch discards the current iteration's operands and reinstalls the loop instruction. A separate native entry step opens the same checked body using the active frame and live Memory32. A zero test completes normally and opens the enclosing tail. The preserved invariant proves exact successors and arbitrary finite-prefix readback from ordinary entry, with no bound on the number of re-entries. Fixtures check the host again after restart, a later host seeing the saved operands, local and latest bytes, a trap after restart, and rejection of invalid target depth or restart payload. | While a source loop is live, normal completion reaches a checked value boundary. Host-region prefixes can read active locals. Indexed source loops, arbitrary graph suffixes within a live host loop, indirect hosts, whole-module validation and infinite runs remain separate. |
| [Checked scalar-result loops in V1 host regions](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/Ranked/Graph/Memory32/Run/Host/Sequence/Thms.lean) | An unindexed parameterless loop may declare one scalar fallthrough result. Its native label arity and checked branch input remain zero independently of that result. A taken back-edge drops iteration operands, reinstalls the loop instruction, and re-enters with an empty inner stack. Normal completion delivers exactly the declared scalar above the saved outer prefix. Both transitions preserve the active frame, locals and live host-updated Memory32. Exact successors and arbitrary finite-prefix readback start at ordinary entry. The fixture restarts with an i32 available, then completes normally and delivers the i32 and saved i64 to a later host with the second iteration's bytes. Static controls reject a scalar restart payload and a mismatched fallthrough type. | Indexed loops, arbitrary graph suffixes inside a live host loop, indirect hosts, whole-module validation and infinite traces remain separate. |
| [Indexed Lime1 loop boundary with host semantics](../../Silmaril/Wasm/Institution/Operational/Loops/Indexed/Thms.lean) | Exact native entry uses the active frame's type table and moves the ordered parameter suffix into the new label. A depth-zero restart delivers the parameter suffix above the saved operands and reinstates the loop for a separate entry step. Normal completion delivers the distinct typed result list and drops the restart continuation. Each control step retains the live store and frame under any supplied host relation. A native regression starts at a source call, restarts with an i64 produced by a host, then passes a different i32 fallthrough result and saved i64 to another host with the latest bytes. Controls cover a missing index and incompatible signature, parameters and results. | The local theorems take typed suffixes as premises. The checked direct-host profile in the next row derives them from ordinary entry. V1 cannot encode indexed loops. |
| [Checked direct hosts in a Lime1 indexed loop](../../Silmaril/Wasm/Institution/Operational/HostCall/Lime1/IndexedLoop/Thms.lean) | Ordinary source entry links the exact root allocation, active module type index, loop producer and one consulted memory slot. Nonzero restarts with the producer's i64 and current store. Zero delivers the i32 result above the saved i64 and derives the checked continuation's initial stack and active local types. Exact successors and arbitrary finite readback start at the ordinary source call and include native loop, label and frame steps. The regression reaches the second iteration from a host-produced parameter, then observes two later host sites, normal return to the caller and alternate traps in the loop and its continuation. | The loop still has one i64 parameter, one i32 result and one direct producer. The checked suffix below runs after loop exit. Indirect hosts, memory instructions or growth, general structured control and whole-module validation remain separate. |
| [Checked Lime1 host continuations](../../Silmaril/Wasm/Institution/Operational/HostCall/Lime1/Continuation/Thms.lean) | The checker follows the ordered stack through local reads, numeric drops and direct hosts. Direct resolution uses the active module and base allocation. Host return replaces the typed operand suffix above the saved prefix and keeps the live Memory32 under the existing [embedding contract](../../Silmaril/Wasm/Institution/Operational/HostCall/Lime1/Thms.lean). Returned traps carry the returned bytes. The straight-line fixture reaches two continuation hosts after loop restart and checks local reads, saved operands, both store outcomes and caller restoration. | Local writes, other numeric operators, indirect hosts, memory growth, whole-module validation and infinite traces remain separate. |
| [Checked nested Lime1 conditionals](../../Silmaril/Wasm/Institution/Operational/HostCall/Lime1/Continuation/Thms.lean) | The suffix grammar admits finite nesting and sequencing of scalar and indexed `if` instructions. For an indexed conditional, the active module's type table supplies the complete numeric parameter and result lists. Both arms check from the ordered parameters to the ordered results. The native i32 choice keeps the parameter suffix in the enclosing stack until a separate block-entry step moves it into a label with the declared result arity. Each label retains its own saved operands and checked tail. Normal exit delivers the arm's results above the saved prefix in one native label step. Trap cleanup exposes and erases each skipped tail in native order while retaining the returned bytes. Exact successors and arbitrary finite readback from ordinary entry cover both indexed arms, an alternate outer arm, and an inner trap past both labels. The fixture uses i32/i64 parameters and i64/i32/i64 results, and rejects mismatched type lookup, insufficient or mismatched parameters, and an incompatible alternate result. | The checked suffix uses a fixed Memory32 and direct hosts under the embedding contract. Suffix loops or general branch dispatch, indirect hosts, memory growth, whole-module validation and infinite traces remain separate. |
| [Checked Lime1 conditional branches under explicit suffix labels](../../Silmaril/Wasm/Institution/Operational/HostCall/Lime1/Continuation/Thms.lean) | The suffix checker resolves `br_if` depth against the active explicit label result signatures and checks the ordered payload suffix and zero-path continuation. The native i32 test consumes only the condition. On a nonzero test, each intervening label discards its own tail and lowers the depth, exposing the pending branch with the saved operands and original stack. At depth zero the native label step discards the target tail and scratch operands, delivering only the ordered result payload above the target's saved prefix. Exact successors and arbitrary finite readback start at ordinary entry, retain the live host-updated store, and distinguish branch transfer, normal label completion and trap unwind. A depth-one fixture transfers i64/i32 results to a later host. Its zero path invokes both intervening hosts and reaches the same later site with different values and bytes. Static controls reject a depth beyond the function label and a reversed payload. | Explicit conditional result labels in the fixed Memory32/direct-host suffix. The implicit function target is covered below. |
| [Checked Lime1 suffix branches to the implicit function label](../../Silmaril/Wasm/Institution/Operational/HostCall/Lime1/Continuation/Thms.lean) | A source `br` and the nonzero successor of `br_if` share the same typed dispatch. The function's ordered numeric results form the final target in the label stack. Ordinary invocation resolves the function's signature separately from the loop index, and the implicit label and frame use the declared function result arity. Each native transfer through an explicit label lowers the depth. Transfer from the implicit label drops the remaining suffix and scratch operands, leaving just the ordered results inside the callee frame. A separate native frame step restores the caller with the live host-updated bytes. Exact successors and arbitrary finite readback include both administrative stages. A regression reaches both branches at depth two with an i32/i64 function result, distinct from the loop's i64 input and i32 result. Zero `br_if` continues through the skipped hosts, and the checker rejects an incomplete or reversed function payload. | Fixed Memory32 and direct hosts under the embedding contract. Suffix loop targets, branch tables, indirect hosts, growth, whole-module validation and infinite traces remain separate. |
| [V1 indirect-call resolution](../../Silmaril/Wasm/Institution/Operational/CallResolution/Indirect/V1/Thms.lean) | The exact native step consumes the unsigned i32 selector and reads the caller's allocated table at slot zero. It preserves arguments, saved operands, continuation, frame, and store. Bounds and uninitialized entries trap before consulting the type index. An initialized slot requires an allocated function and an exact declared parameter and result type. A type mismatch traps. An absent table, type, or function where consulted has no lookup successor. [Wasm 1.0 indirect call](../../specs/spectec/src/specification/wasm-1.0/8-reduction.spectec#L116) | Callee steps and caller resumption use the guarded context below. |
| [V1 indirect call to a checked Memory32 callee](../../Silmaril/Wasm/Institution/Operational/CallResolution/Indirect/V1/Context/Thms.lean) | At one designated external site with a fixed table and an exact module type, all initialized entries refer to allocated non-host functions in the checked graph. A successful lookup feeds its typed ordered argument suffix into the existing V1 invoke and frame correspondence. Exact steps and finite prefixes read back the callee through delivery or trap while retaining the caller's stack, locals, and one live memory. The checked readback ends at the callee boundary and uses native steps for the caller tail. A regression reaches a nonzero-offset callee write and reads it from the resumed caller, under either direct-call policy. | The graph-body profile is covered below. Mutable or multiple consulted tables, host calls, later-version signatures, multiple mutable memories, whole-module validation, and infinite executions. |
| [Indirect calls inside checked V1 Memory32 graph bodies](../../Silmaril/Wasm/Institution/Operational/CallContinuation/OuterCall/Ranked/Graph/Memory32/Run/Thms.lean) | Source sites under typed control bind the active module's slot zero to the fixed allocated Table32 and resolve its exact declared parameter and result lists. The checker inspects sites in skipped code and requires a graph declaration at each initialized entry. Ranked mode requires strict descent for entries with the matching signature. A mismatching entry traps regardless of rank. The opt-in recursive policy uses the same frame and result correspondence without descent. Each native lookup becomes one graph edge, then an ordinary pending invocation or a trap. Native and checked finite prefixes agree through caller resumption and memory effects. A reached bounds, uninitialized-entry, or signature trap unwinds the live block and function frame, retains the earlier write, and skips the caller tail. | Host calls, mutable or multiple consulted tables, later-version signatures, multiple mutable memories, whole-module validation, and infinite executions. |
| [Checked indirect-call resolution](../../Silmaril/Wasm/Institution/Operational/CallResolution/Indirect/Native/Thms.lean) | Core and Lime1 read a fixed allocated Table32 at module slot zero. Exact successors consume the unsigned i32 selector while retaining the numeric operands and pending continuation. Bounds, null, and signature mismatch have separate checked outcomes. Successful lookup enters the allocated graph function on its ordered numeric argument suffix. | The separate contextual theorem below applies after successful resolution. Other table profiles, host targets, and V1 remain open. |
| [Indirect-call contextual readback](../../Silmaril/Wasm/Institution/Operational/CallResolution/Indirect/Context/Thms.lean) | A successfully resolved Table32 site enters a checked, allocated Core or Lime1 graph callee. Exact native prefixes include four Core steps or two Lime1 steps through frame entry, arbitrary finite prefixes of cyclic direct calls, ordered return above the saved caller operands, and trap discard up to the bare caller trap. | Execution of the resumed caller instructions, indirect calls in graph bodies, mutable tables or stores, host calls, and V1. |
| [Checked resumption after an indirect call](../../Silmaril/Wasm/Institution/Operational/CallResolution/Indirect/Context/Resume/Thms.lean) | One designated Table32 site under an entered function label in Core or Lime1. Exact lookup through the first native trap or pending invocation. For a successful lookup, every finite native run reads back through callee execution, the typed caller tail, and the caller function exit, including callee traps and arbitrary finite recursion inside either checked direct-call fragment. | Source `call_indirect` inside graph bodies, exact failed-lookup cleanup beyond the first trap, arbitrary enclosing label positions, mutable tables or stores, host calls, and V1. |
| [Checked indirect source regions](../../Silmaril/Wasm/Institution/Operational/CallResolution/Indirect/Source/Thms.lean) | A single typed indirect operator after a numeric prefix, optionally inside parameterless scalar blocks with checked graph tails. Preparation resolves the current activation's module type index and Table32 address. Exact Core and Lime1 lookup and successful callee entry preserve already-entered block contexts. The source guard supplies the checked resumption theorem at a function label. | Installing the operator in cyclic graph function bodies, native evaluation from the start of the source region, and nested post-entry return and trap readback. Mutable tables and stores, host calls, whole-module execution, and V1 remain separate. |
| [Indirect graph source entry](../../Silmaril/Wasm/Institution/Operational/CallResolution/Indirect/GraphEntry/Thms.lean) | One designated allocated graph address computes the ordered arguments and i32 selector with a checked local-read and integer-op prefix before a typed Table32 site. The site can be in the function label or under a finite spine of parameterless scalar blocks with a checked result and enclosing continuation at each level. Exact Core and Lime1 finite readback starts at an ordinary direct `call` and reaches caller exit or ordered trap cleanup. | Conditional entry uses the separate profile below. Paths through loops or branches, re-entry to the indirect body from graph dispatch, mutable tables or stores, host calls, whole-module execution, and V1. |
| [Conditional indirect graph entry](../../Silmaril/Wasm/Institution/Operational/CallResolution/Indirect/GraphEntry/Conditional/Thms.lean) | An i32 local selects a scalar if arm at the function label. Either arm may hold the designated site under the checked block spine. Both arms and the shared continuation are typed. Exact Core and Lime1 finite readback follows the chosen arm from ordinary invocation through return or trap. The alternate arm uses the direct graph relation and needs no native table allocation. | Conditional paths below entered blocks use the recursive profile below. Loops or branches on the path to the site, recursive dispatch back to the indirect body, mutable tables or stores, host calls, and V1. |
| [Recursive control path to an indirect site](../../Silmaril/Wasm/Institution/Operational/CallResolution/Indirect/GraphEntry/Control/Thms.lean) | One designated site under a finite composition of immediately nested parameterless scalar blocks and i32-local conditionals. Every conditional checks its alternate arm against the same block result and the enclosing continuation. Each selected arm lowers to one block, preserving active locals, saved operands and entered labels. Core and Lime1 read back from typed entry through either the site or the first selected alternate and its enclosing continuations. | Loop entry and restart on the source path, branch dispatch to the site, redispatch into an indirect body, mutable tables or stores, host calls, and V1. |
| [Recurrent loop entry to an indirect site](../../Silmaril/Wasm/Institution/Operational/CallResolution/Indirect/GraphEntry/Loop/Thms.lean) | A parameterless void loop writes an i32 local, tests its old value with `br_if 0`, and either reinstalls the source loop or chooses the site or empty arm. Core and Lime1 exact finite readback distinguishes branch, reinstatement and re-entry, including arbitrarily many restarts. The empty arm restores the saved operands and runs the checked function tail without a native table. The site arm has exact numeric-prefix and first-lookup readback under the active loop, through a pending invocation or the first lookup trap. | Callee return and trap cleanup use the resumption profile below. Repeated lookup, general loop bodies and branches around the designated site, recursive dispatch into the indirect body, mutable tables or stores, host calls, and V1. |
| [Indirect-call resumption under the live loop](../../Silmaril/Wasm/Institution/Operational/CallResolution/Indirect/GraphEntry/Loop/Resume/Thms.lean) | A selected computed Table32 site enters its checked direct graph callee in Core and Lime1. Exact finite readback continues through ordered return, typed writes to the active frame’s locals, the arm and loop exits, and the enclosing checked function tail. Lookup and callee traps discard operands and pending code at their active labels before leaving the caller frame. | The selected arm admits a checked list of local writes after return. Repeated lookup, broader arm code and loop bodies, recursive indirect redispatch, mutable tables, host calls, and V1 remain separate. |
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
the ranked judgment on that domain. The separate V1 shared-Memory32 profile has an opt-in recursive checker.

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

A designated indirect site can also execute within one already-entered
function's label. The caller continuation is checked against the site's
declared result types above the saved operand types, the caller's current
locals, and the enclosing function signature. It may use the existing checked
graph body operations and direct-call targets. A successful lookup gives exact
native finite readback through the checked tail and the caller function exit.
A callee trap resumes at the caller's trap-discard state. The return fixture
executes a pending local read and delivers the result to a distinct outer
frame. The trap fixtures cover a callee trap and an unsigned bounds failure.
The exact failed-lookup theorem stops at the first native trap, preserving
pending Core lowering instructions until native discard.

The standalone source-region checker now checks one typed indirect operator
after a numeric prefix, possibly inside parameterless scalar blocks. The
selector must be an i32 above the ordered argument suffix. Each activation
uses its own module's type index and table slot zero, whose address must be
present in the fixed allocation. Missing types, tables, and declarations
fail preparation. In-bounds null entries, unsigned out-of-bounds selectors,
and valid targets with incompatible signatures remain native lookup traps.
The fixtures use two modules with different type entries and table addresses.

Exact lookup and successful entry hold under already-entered scalar labels,
preserving each label's saved operands and pending instructions. At a
function label the checker supplies the typed resumption premises above. The
source-region checker also supplies the guard for one designated graph entry
with a checked numeric prefix and an indirect site in the function label or
inside a finite spine of immediately nested parameterless scalar blocks.
The native store
contains the actual indirect source code at that graph address. The checked
direct-call graph supplies the registered declaration and continuation typing.
Native allocation is checked at linked direct targets and at table entries
used by lookup. This lets the callee and resumed tail use dynamic recursive
frame descent without requiring the designated entry's body to be direct code.

The graph-entry proof starts at an ordinary typed `call` and records both
steps through entry of the outer function. Each block enters in a separate
native step and starts its body on an empty stack. The outermost block saves
the function's initial operands. The operand prefix reuses the graph's typed
local reads and integer binary operations on that frame's locals and
the active operand stack. Each prefix state records its remaining code. Successful
evaluation passes the saved stack prefix, ordered arguments, and i32 selector
to the existing lookup relation. From there Core takes four steps to successful
callee entry and Lime1 takes two. A numeric trap leaves the unevaluated
prefix, the indirect instruction, and the active label's tail pending for
native discard, using only the entry function's allocation.

Exact finite readback includes ordered resumption, recursive prefixes inside
checked direct callees, and cleanup of prefix and lookup traps through
function exit. Core lookup-trap cleanup also retains pending lowering
instructions until they are discarded. The fixtures exercise mixed-width
return, success and null selection from the same table by varying a local,
bounds and signature mismatch, partial prefix steps, division by zero before
lookup, and arbitrarily deep finite direct recursion after the indirect site.

At a nested site, a successful call delivers its results in order to the
innermost tail. The graph relation checks and executes each enclosing tail
with its label's declared result and saved operands. A trap first discards
the innermost operands and instructions. Each label exit then exposes the
next set of operands and pending instructions for discard. The three-block
fixture performs arithmetic and writes locals across the label exits before
the function tail reads them. Its trap cases distinguish a prefix failure
before lookup from a null lookup and check an intermediate unwind state.

The conditional entry profile reads an i32 local above the function's saved
operands and lowers the selected arm to one scalar block. Either arm may
contain the site under its checked block spine. The alternate arm is checked
as ordinary graph code against the same scalar result and shared tail. Its
native readback uses the function allocation and direct links, including in
a store without the statically described table. A selected-site path uses the
same numeric, lookup, callee and discard relations as block-only entry. The
fixtures exercise both selections, division by zero in the selected site,
null lookup, and rejection of an ill-typed arm even when skipped.

The recursive control path records the entered block context alongside the
remaining source nodes. Each conditional checks both arms, and its selected
arm lowers to a block in the same activation. An alternate arm transfers to
the direct graph relation under the labels already entered. The two-if
fixture interleaves a block, selects the inner alternate without a native
table, and observes its result through the outer tails. The selected-site
fixture observes a mixed-width return and an intermediate unwind where the
outer label still holds its saved operand. The table allocation premise is
needed only for lookup, including when the lookup itself traps.

The recurrent loop profile checks a parameterless void loop with an i32
local write followed by a depth-zero conditional branch. A nonzero old value
reinstalls the original loop in its own native step, preserving the updated
locals and saved operands. A zero test chooses either a checked numeric
prefix and indirect lookup or an empty arm that exits into the checked
function tail. Finite runs use the recurrent relation, which permits any
number of restarts. Native table allocation enters only in the lookup
theorems. The fixture reads the updated local as the first selector after
a restart, distinguishing the null slot from the original out-of-bounds
index. Another path returns the saved i64 and updated i32 without a table.

The loop resumption profile composes the first selected lookup with the
resolved target's checked direct graph, including finite recursive callee
prefixes. A checked list of local writes consumes the ordered return values
and saved site operands. The arm and live loop exit in separate steps,
restoring the loop’s saved operand prefix and preserving the enclosing frame and
resuming the ordinary checked function tail. Lookup traps start cleanup in
the arm. Callee traps first leave the callee label and frame, then run the
same arm, loop, and caller discard rules. The fixtures reach all three
outcomes after a restart and observe the mixed-width returned values and
saved operands in the restored caller.

Further lookup on subsequent trips, general arm and loop bodies, arbitrary
branch dispatch to the site, and recursive entry into an indirect body remain
separate. The checked direct continuations retain their existing graph coverage.
[Source-region theorems](../../Silmaril/Wasm/Institution/Operational/CallResolution/Indirect/Source/Thms.lean)
and [graph-entry theorems](../../Silmaril/Wasm/Institution/Operational/CallResolution/Indirect/GraphEntry/Thms.lean)

The pinned Wasm 1.0 reduction snapshot provides direct source resolution and
Wasm-function entry. The host-call bridge uses the repository's separate native
embedding interface, including the declared divergence outcome. It covers
void or scalar numeric results and requires the embedding's proof of typing
and its chosen store relation at the checked input. The finite theorem reads
back the selected call through delivery and represents subsequent caller
execution with native steps.
[Wasm 1.0 call rules](../../specs/spectec/src/specification/wasm-1.0/8-reduction.spectec#L113)
· [Native host callout](../../Silmaril/Wasm/V1/Execution/Callout.lean)
· [Checked host boundary](../../Silmaril/Wasm/Institution/Operational/HostCall/V1/Thms.lean)

The shared legacy baseline uses the native public Wasm V1 and Lime1 relations.
Lime1-specific multi-value and bulk-memory cases and newer Core features have
separate obligations. Whole-module validity and execution, initialization,
general host interaction, divergence correspondence, and maximal observations
remain separate.
See the [native version injections](wasm-version-injections.md) and the
[SpecTec snapshot manifest](../../specs/spectec/manifest.json).
