# Sea of Nodes tail-tested memory loop

IR ’95 §2.5 models the whole STORE as an SSA value that a Phi can merge.
Sections 3.1–3.2 and Figure 7 show a Loop Region latching by the arriving
control occurrence, with a tail If whose true projection goes back to
the header. Simple chapter 10 closes a loop's memory Phi with the memory
produced in the body. Its example uses a header test. This fragment uses
the paper's tail test and the same occurrence-to-memory correspondence.
[IR ’95](https://doi.org/10.1145/202530.202534) ·
[Simple chapter 10 at `f0a6c675`](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#memory-is-an-ssa-variable)

The entry occurrence selects Start's initialized heap. The backedge
occurrence selects the preceding activation's final memory version. The
selected heap is memory version zero for the next activation's ordered
straight-line table. Each table contains a Load and a Store. The word
it exports is the tail If's data input. Comparing it to a typed invariant
word argument determines exit on equality and a backedge otherwise. The
exit observes that word and the latest heap. Zero backedges still execute
the table once.
[Definitions](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Defs.lean) ·
[Straight-line memory profile](sea-of-nodes-memory.md)

Import `Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms` for
`Graph.returns_iff_mem_denote`. It identifies finite explicit-edge returns
with membership in the heap-threaded partial denotation, observing the
word and whole final heap. `Graph.returnsAfter_iff_evalAfter` adds an exact
completed-backedge count. The executable `evalAfter` yields `none` when
there is no return at that count. The model fixes the table's effect order
and uses already initialized word cells. It covers one header and one
backedge with a total body and total test.
[Theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Thms.lean)

The regression shifts one initialized cell into another and clears the
source cell. The one-activation case still performs both stores. In the
two-backedge case the first activation loads `1` and writes `2` to the same
address. The next activation loads that `2`, and the third loads `0` and
exits. The checks observe the entire final heap and its untouched cell.
[Regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Loop.Defs
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Regression
```

## Typed MLIR CF lowering

```lean
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Thms
```

`MLIR.lower` shares the [finite-cell body compiler](../../../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/MLIR/Finite/Defs.lean).
The fixed, initialized `Fin n → Word` heap is carried as `n` scalar `i64`
block arguments. The ordered body emits scalar scans for dynamic typed
addresses. Entry passes the initial heap to the header. The header runs
the body and forwards the returned word and updated heap to the test
block. The test emits `arith.cmpi eq` against the invariant typed stop word.
Its backedge feeds the updated heap into the header, and its other edge
passes the word and heap to exit. This is an SSA encoding of initialized,
in-bounds cells with a fixed cell count.
[CFG definitions](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/MLIR/Defs.lean)

`MLIR.lower_run_eq_some` gives the exact minimum `Cfg.run` budget of
`2 * k + 4` block ticks for a return with `k` completed backedges. `MLIR.lower_returns_iff` matches finite returns of the word and
entire heap. `MLIR.lower_denotePart` gives the corresponding observation
in the [existing partial CF evaluator](../../../../Silmaril/SSA/MLIR/CF/SwitchAssert/Denotation/Defs.lean),
and `MLIR.lower_diverges_iff` matches absence of any finite return.
[CFG theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/MLIR/Thms.lean)

The emitted-CFG checks exercise the three-cell shift with zero and
two backedges, a removed store that preserves the word and changes the
final heap, and a fixed backedge with no finite return.
[CFG regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/MLIR/Regression.lean)

### Equations at typed entry valuations

```lean
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Institution.Thms
```

`MLIR.Institution.satisfaction` compares the two emitted CFGs using
the canonical scalar profile at the native model's cell count. It
preserves and reflects agreement on every initial heap, including
the absence of a finite return. `observe_mapGraph` and
`satisfaction_reindex` relate re-emission after a typed entry port map
to pullback of the native valuation, with the same heap and cell count.
These laws compare observations of generated CFGs over the existing
native models.
[Native institution](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Institution/Thms.lean) ·
[MLIR equation theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/MLIR/Institution/Thms.lean)

### Compare emitted backend observations

```lean
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Thms
```

At a shared typed entry valuation and initial heap,
`lambda_observation_iff_mlir` identifies the λSSA return at label zero
with the CF observation of its packed word and whole final heap.
`mlir_observation_eq_map_theta` re-encodes the numbered θ result by
reading its word and heap wires into the scalar CF result tuple.
`mlir_observation_iff_run` connects that partial CF observation to
finite execution of the emitted CFG.
[Backend comparison](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Institution/Lowering/Backends/Thms.lean)

`lambda_no_return_iff_mlir` and `theta_no_return_iff_mlir` match
absence of finite returns. The corresponding satisfaction laws
compare equations over all initial heaps at the chosen valuation.
The regression checks the three-cell result after two backedges
and the absence of a result in all three backends on a fixed backedge.
[Regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/Institution/Lowering/Backends/Regression.lean)

The CF evaluator runs scalar bindings with a total bitvector
interpretation. The LLVM scalar profile rejects `llvm.load`.
The MLIR result in these laws uses the initialized cells carried
as SSA values above.
[CF evaluator](../../../../Silmaril/SSA/MLIR/CF/Basic/Defs.lean) ·
[LLVM admission example](../../../../Silmaril/SSA/MLIR/LLVM/Examples/Thms.lean)

## Typed MemRef activation

`MemRef.lowerActivation` reuses the [single-buffer body lowering](sea-of-nodes-memory.md#one-initialized-rank-one-memref).
It emits the native ordered `memref.load` and `memref.store` bindings
and appends `arith.cmpi ne` to compare the body's returned word with
the invariant stop operand. The comparison uses the ordered block's
two-way control type. Selector zero requests exit and selector one
requests a backedge. The monadic runtime carries every updated buffer
cell in either case.
[Activation definitions](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/MLIR/MemRef/Defs.lean) ·
[Ordered control syntax](../../../../Silmaril/SSA/RVSDG/MLIR/Graph/Feedback/Defs.lean) ·
[Pinned comparison operation](https://github.com/llvm/llvm-project/blob/4434dabb69916856b824f68a64b029c67175e532/mlir/include/mlir/Dialect/Arith/IR/ArithOps.td)

`lowerActivation_run` identifies the emitted selector, word, and complete
buffer. `observeActivation_eq_step` decodes the outcome and identifies it
with the native heap-threaded step for any starting buffer. This is a
one-activation law for one initialized, contiguous, statically sized
rank-one `i64` buffer with `Fin n` indices.
[Activation theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/MLIR/MemRef/Thms.lean)

The activation regression also passes a restart buffer into a second
activation. Its one-cell case uses coincident indices and checks that
the last store wins. The same fixture requires a typed address, so its
entry valuation is uninhabited at zero cells.
[Regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/MLIR/MemRef/Regression.lean)

### Executing MemRef feedback

`MemRef.runAfter` repeatedly executes that emitted activation. An exit
returns the loaded word and whole final buffer. A backedge passes the
post-store buffer to the next activation with the original typed operands.
The budget counts **exactly** the requested backedges, so even budget zero
executes the entry activation and an earlier exit yields `none` at a larger
count. `MemRef.observe` describes the finite return across all counts.

The driver repeats the emitted ordered block using the decoded activation
outcome.
[Driver definitions](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/MLIR/MemRef/Feedback/Defs.lean)

`runAfter_eq_evalAfter` agrees with the native evaluator at every exact
count. `returnsAfter_iff_runAfter` and `returns_iff_mem_observe` preserve
and reflect the word and every cell in counted and finite returns.
`observe_eq_none_iff` identifies the absence of a finite return with
`none` at every count.
[Feedback theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/MLIR/MemRef/Feedback/Thms.lean) ·
[Feedback regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/MLIR/MemRef/Feedback/Regression.lean)

### Emitted MemRef CF loop

`MemRef.CF.lower` emits a typed CFG with an entry branch, a header
conditional, and an exit return. Its header contains the same emitted
ordered MemRef activation. The typed entry valuation is captured by the
body interpretation, and the initialized buffer lives in `StateM`.
The activation's selector becomes an `i1` terminator operand. The
conditional takes a self edge on restart and passes the `i64` word
to the exit on completion. Both edges carry the whole updated buffer
through the shared monad.
[CFG definitions](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/MLIR/MemRef/CF/Defs.lean) ·
[Ordered CF adapter](../../../../Silmaril/SSA/MLIR/CF/Ordered/Defs.lean)

`header_transition` identifies both actual successor frames and their
post-store buffer. `run_eq_some_iff` agrees with the exact-count driver
at any count within the CFG's backedge allowance. The CFG runner uses
one block step each for entry and exit and one per header activation.
The shared scheduler specializes to the pure CF evaluator via
`runBlock_id`.

At the native boundary, `Buffer.mk heap` uses the native `Fin n → Word`
heap as its cell function, and the typed input valuation is shared.
`cfg_run_eq_some_iff_returnsAfter` observes the returned word and every
cell exactly when a native return at count `k` fits the raw block fuel
(`k + 3 ≤ fuel`). The `run` wrapper uses `budget + 3` blocks, so
`run_eq_some_iff_returnsAfter` uses `k ≤ budget`. `run_eq_none_iff`
identifies bounded absence with failure at every native exact count
within that allowance. Across all allowances,
`exists_run_eq_some_iff_mem_denote` and
`forall_run_eq_none_iff_denote_eq_none` give finite observation and
no-finite-observation agreement with the native partial denotation.

This profile covers one initialized rank-one buffer with in-bounds
indices. Textual MLIR emission and general MemRef effects remain outside
the profile.
[CFG theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/MLIR/MemRef/CF/Thms.lean) ·
[Pure specialization](../../../../Silmaril/SSA/MLIR/CF/Ordered/Thms.lean) ·
[CFG regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/MLIR/MemRef/CF/Regression.lean)

### Equations for emitted MemRef CF

`MemRef.CF.Institution.observe` collects finite returns of the emitted CFG
as a partial word-and-heap value at the native model's cell count and
typed entry valuation. `observe_eq` identifies that value with the native
partial denotation, including absence of a finite return.
`satisfaction` gives both directions of equation truth over all initial
heaps. `observe_mapGraph` and `satisfaction_reindex` reuse the native
typed entry-port maps and valuation reduct.
[MemRef equation theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/MLIR/MemRef/CF/Institution/Thms.lean)

`mlir_observation_eq_map_memref` packs the MemRef result's word and every
cell into the scalar CF backend's partial observation.
The regression rejects two emitted programs with the same returned word
and different final heaps, and checks the absence of a finite return.
[Backend theorem](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Institution/Lowering/Backends/Thms.lean) ·
[Equation regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/Institution/Lowering/Backends/Regression.lean)

### Compare emitted MemRef CF and numbered θ

At the same native typed valuation and initial heap,
`memref_observation_eq_map_theta` reads the emitted θ result's word and
whole heap wire into the MemRef CFG's partial observation.
`memref_observation_iff_theta_returns` relates a defined observation
to an actual finite return of the numbered graph.
`memref_run_iff_theta_run` converts successful execution witnesses in
both directions. A common native return after `k` backedges admits
`k + 3` CF block steps and `k + 1` θ activations.
`theta_no_return_iff_memref` matches absence of a finite return.
`theta_satisfaction_iff_memref` compares satisfaction and composes with
the existing typed reindexing laws on either backend.

The regression executes the three-cell shift with two backedges in both
backends. It checks the word, two changed cells, and the untouched cell,
and exercises the no-return case and typed address reindexing.
[Backend comparison](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Institution/Lowering/Backends/Thms.lean) ·
[Regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/Institution/Lowering/Backends/Regression.lean)

### Compare coloured Petri completion and MemRef CF

At the same typed model and initial heap, `petri_completion_iff_memref`
identifies a completed firing trace of the emitted memory θ with the
MemRef CFG's partial return of the same word and whole heap.
`petri_completion_iff_memref_run` gives the corresponding finite CFG
execution witness. `petri_no_completion_iff_memref` compares absence
of any completed firing trace with absence of a finite MemRef return.
Firing traces and CFG block fuel are separate witnesses.

The regression uses the portable two-backedge completion and the
emitted MemRef execution of the three-cell shift. Both updated cells
are observed, and a completion that changes the untouched sentinel
is ruled out even with the same return word.
[Coloured completion](../../sea-of-nodes-memory-loop-petri.md) ·
[Backend theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Institution/Lowering/Backends/Thms.lean) ·
[Regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/Institution/Lowering/Backends/Regression.lean)

### Interleaved effects at the feedback boundary

The native profile admits dependent Loads and Stores in a single ordered
body. Each memory edge must name the current whole-heap version, and the
tail test compares the result word with a fixed typed input. Addresses
are invariant entry ports in this profile. The boundary law covers
aliasing among those ports. Computed addresses and arm-local memory
control inside a loop activation are outside this source profile.

`petri_activation_iff_memref_header` compares the actual coloured
activation's output with the emitted CF header's successor frame and
whole buffer. Tag one selects the header and passes the post-store
buffer. Tag zero selects the exit with the invariant stop word. Each
activation starts at the same heap and typed operands.

The regression alternates three Loads and three Stores. With distinct
addresses, the final Load reads the saved word and takes a backedge
with cells `[0, 7]`. The next activation reads the updated buffer and
returns with cells `[0, 0]`. With aliasing addresses, the final Load
sees the clear immediately, selects the exit, and the last Store
restores the saved word, leaving cells `[7, 99]`. A coloured firing
completion and a CF header step are separate witnesses.
[Activation theorem](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Institution/Lowering/Backends/Thms.lean) ·
[Interleaved regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/Institution/Lowering/Backends/ActivationRegression.lean)

### Address Phi at the feedback boundary

`CarriedAddress.Graph` specializes the [typed Loop Phi operand columns](../../../../Silmaril/SSA/SeaOfNodes/Loop/Defs.lean)
to one address in the ordered memory body. The entry and backedge columns
each name an input port of address sort. Their values are `Fin cells` in the
same initialized heap. The other operands stay invariant, and feedback
supplies the previous activation's entire post-store heap.
[Source definitions](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/CarriedAddress/Defs.lean)

`CarriedAddress.MemRef.lower` emits an ordered typed CFG. The entry branch
passes zero to an `i1` header argument, and the conditional self edge passes
one. The header resolves that occurrence to one of the captured in-bounds
addresses and runs the existing ordered MemRef Load/Store activation with
it. The exit edge passes the return word, and both successor edges retain
the entire buffer in the shared state.
[CFG definitions](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/CarriedAddress/MemRef/Defs.lean)

`header_transition` gives the exact successor label, arguments, and buffer
at either arrival. `run_eq_evalWithin` compares a native backedge allowance
`k` with `k + 3` CF block steps. `petri_activation_iff_header` compares one
existing coloured activation seeded with the selected typed inputs to
that header transition. Computed address operands and control inside the
ordered body remain open.
[Theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/CarriedAddress/MemRef/Thms.lean)

```lean
import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.MemRef.Thms
```

The executable regression enters with `[7, 0, 99]`, writes cell 0, and
restarts with `[9, 0, 99]`. The next activation reads cell 1, writes it,
and exits with word `0` and cells `[9, 9, 99]`. The same checks cover
immediate exit, an exhausted backedge allowance, and coincident ports.
[Regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/CarriedAddress/MemRef/Regression.lean)

#### Emitted coloured loop with the address Phi

`CarriedAddress.Petri.lower` emits one numbered θ with a γ in its body.
The θ carries the occurrence colour, invariant typed input tuple, and one
initialized heap. The γ arms reuse the ordered Load/Store activation with
the leading address wired to the corresponding input port. The arm's
continuation tag supplies both the θ decision and the next occurrence. On
feedback, the existing `Fire.restart` rule installs occurrence one and the
whole post-store heap in the next activation. The root receives
`encodeArrival .entry heap input` once.
[Lowering definitions](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/CarriedAddress/Petri/Defs.lean)

`lowerBody_run` gives the complete successor tuple.
`lower_finishes_iff` identifies finite completion from the single entry
marking with a native return of the word and every final cell.
`finishes_iff_memref_run` and `no_finishes_iff_memref_none` transfer finite
completion and its absence to the emitted MemRef CFG. A native allowance
of `k` backedges uses `k + 1` numbered θ activations or `k + 3` MemRef CF
block steps. The coloured result has a separate finite firing-trace
witness.
[Completion theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/CarriedAddress/Petri/Thms.lean)

```lean
import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Petri.Thms
```

The shared three-cell fixture proves completion of the emitted net from
one marking, with the cell 0 → cell 1 transition and the full result
`(0, [9, 9, 99])`. It also proves immediate-exit completion and executes
the numbered graph with distinct and coincident ports.
[Regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/CarriedAddress/Petri/Regression.lean)

#### Equations for the address Phi

`CarriedAddress.Institution.inst` uses the existing memory entry
signatures, typed port maps, and models. A model chooses the cell count
and entry valuation. An equation compares complete finite word-and-heap
observations for every initialized heap at that model. Two absent
observations agree at that heap. Each port map renames both Phi operands
and the invariant inputs under the bound address.
[Equation definitions](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/CarriedAddress/Institution/Defs.lean)

`petri_satisfaction` and `memref_satisfaction` preserve and reflect
native satisfaction using the emitted coloured graph and MemRef CFG.
Their reindexing laws compare re-emission at renamed ports with the
model reduct. `petri_no_return_iff_native` and
`memref_no_return_iff_native` compare absence of any finite result.
A finite firing trace and a CFG backedge allowance witness their
respective observations.
[Equation theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/CarriedAddress/Institution/Thms.lean)

`runtime_satisfaction` also factors the comparison through the
existing nested RVSDG runtime observer at the canonical initialized
heap model and `encodeArrival .entry`. The native model fixes one typed
scalar valuation. The general nested RVSDG equation room quantifies
over every raw input tuple, including both occurrence colours, and its
signature maps relabel opcodes. The address-Phi institution's signature
maps act on entry ports.
[Runtime observation room](../../../../Silmaril/SSA/RVSDG/NestedTheta/Institution/RuntimeObservation/Defs.lean)

```lean
import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Thms
```

The regression uses the shared address-switch fixture for both backends,
checks immediate exit, and proves absence of finite returns at the
coincident-port valuation and initial heap `[7, 0, 99]`. Reversing the
two address operands yields the same word and a different final heap,
so the equation fails at the distinct-port valuation. At the coincident-port
valuation it holds for every heap. Swapping the typed ports and pulling back
the valuation transports the comparison.
[Regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/CarriedAddress/Institution/Regression.lean)

#### Validated runtime entries for address Phi equations

`RuntimeEntry.RawEntry` is the numbered program's typed argument tuple.
Each address is a `Fin cells`, and the heap port contains a word for every
cell at the same size. `decode` accepts occurrence zero and recovers the
scalar tuple and full heap. It refuses feedback colour one. The encode
and decode laws characterize the accepted tuples exactly. A decoded
entry may have an absent finite observation, represented by `Part.none`.
[Entry definitions](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/CarriedAddress/Institution/RuntimeEntry/Defs.lean)

`Agrees` compares existing nested RVSDG programs at this exact typed
boundary in the canonical memory runtime, over all admissible raw
entries at a fixed cell count. For the emitted graphs, `satisfaction`
identifies this comparison with source equation satisfaction at every
typed scalar valuation and initialized heap. The `observe_eq_some_iff_native`
and `observe_eq_none_iff_native` laws transfer complete finite results
and their absence at a decoded entry.
[Entry and equation theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/CarriedAddress/Institution/RuntimeEntry/Thms.lean)

`decode_reindex` commutes with the typed source reduct and preserves the
occurrence and heap. `observe_mapGraph` compares re-emission with that
raw entry pullback. `satisfaction_reindex` ranges over pullbacks of target
valuations. These maps act on typed entry ports of this profile. The
general nested RVSDG room ranges over every raw tuple for its dialect.
[Runtime observation room](../../../../Silmaril/SSA/RVSDG/NestedTheta/Institution/RuntimeObservation/Defs.lean)

```lean
import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeEntry.Thms
```

The regression rejects a feedback-coloured root before and after an
address-port swap, recovers the full entry on a successful round-trip,
and observes the same result after reindexing. An equation whose two
sides return zero with different heaps fails on an admissible entry.
An admissible entry with coincident ports observes `Part.none` once
the heap is fixed at an existing backedge state.
[Regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/CarriedAddress/Institution/RuntimeEntry/Regression.lean)

#### Institution of generated address Phi runtime equations

`RuntimeRoom.room` uses equations between emitted numbered graphs with
their source retained for re-emission. Its models use the existing
typed cell count and scalar valuation. At one such model,
`modelEntry` supplies the validated raw entry for each initialized heap,
and satisfaction compares the exact partial word-and-heap results.
`satisfaction_iff_petri` and `satisfaction_iff_memref` give the same
truth on the emitted backends. Firing traces and CFG budgets remain
independent witnesses.
[Room definitions](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/CarriedAddress/Institution/RuntimeRoom/Defs.lean)

A signature map from `P` to `Q` takes each typed port of `P` to a port of
`Q`. The sentence action re-emits at the target ports, while the model
reduct pulls a `Q` valuation back to `P`, retaining the entry occurrence
and entire heap. `RuntimeRoom.comparison` is a comorphism over these
same typed entry signatures into the generated room. The unrestricted
RVSDG runtime room uses opcode maps and has its own model and entry
quantifiers.
[Room and comparison theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/CarriedAddress/Institution/RuntimeRoom/Thms.lean)

`holds_iff_all_models` connects per-valuation room truth to global
truth at a fixed cell count. After a port map, `holds_map_iff_reduct_models`
quantifies over the image of the target valuation reduct. A map that
identifies two address ports only tests source valuations where those
addresses coincide. The regression checks both a swap that preserves a
whole-heap observation and an identification that makes an equation
globally true at three cells even though its source version is false.
[Regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/CarriedAddress/Institution/RuntimeRoom/Regression.lean)

```lean
import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeRoom.Thms
```

#### Institution of generated address Phi MemRef equations

`MemRefRoom.room` compares emitted ordered MemRef CFGs. At a model's
cell count and typed valuation, each run starts at the root with
`Env []`, the captured typed operands, and one initialized rank-one
`Buffer cells`. The root branch supplies the entry occurrence. Addresses
are `Fin cells`, and the buffer supplies a word for every cell.
Satisfaction ranges over every such buffer. It compares the exact
returned word and full final buffer, with `Part.none` representing
absence of a finite return.
[MemRef Room definitions](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/CarriedAddress/Institution/MemRefRoom/Defs.lean)

`MemRefRoom.comparison` is a comorphism from the native institution
over the same typed entry signatures. Port maps re-emit the CFG
forwards and pull scalar valuations back, preserving the cell count
and initialized buffer. `all_models_map_iff` places global truth after
reindexing over the image of that reduct. The regression checks the
satisfaction condition after an address swap and the change in global
truth caused by identifying two distinct address ports.
[MemRef Room theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/CarriedAddress/Institution/MemRefRoom/Thms.lean) ·
[Regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/CarriedAddress/Institution/MemRefRoom/Regression.lean)

`observe_runtime` encodes the actual MemRef result as the full RVSDG
result at the validated entry, preserving absence as well.
`runtimeComparison` re-emits the sources retained by the generated
RVSDG equations into the MemRef Room. `comparison_factors` identifies
its composition with the native-to-RVSDG corridor, at each signature,
with the native-to-MemRef corridor. These comparisons concern the
generated profile. RVSDG and MemRef retain their own finite execution
witnesses.

```lean
import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.MemRefRoom.Thms
```

#### Shared interface for generated address Phi backends

`Institution.Backend` packages a generated equation family, its
retained native sources, and its own partial observer. An instance
supplies exact encodings of the initialized heap and whole return and
proves finite-result adequacy. `Backend.rvsdg` and `Backend.memref` use
the existing validated nested RVSDG and ordered MemRef observers.
[Interface](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/CarriedAddress/Institution/Backend/Defs.lean) ·
[Instances](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/CarriedAddress/Institution/Backend/Instances/Defs.lean)

`observe_translate` compares the actual emitted partial observations
after decoding the word and all heap cells. Two absent finite
observations agree, and a finite result uses each backend's own
witness. `observe_reemit` compares a forward typed port map with
pullback of the valuation at the same cell count and initial heap.
`holds_reemit_iff_image` characterizes global truth after re-emission
by satisfaction exactly over the reduct image.
[Observation and reindexing laws](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/CarriedAddress/Institution/Backend/Thms.lean)

The shared construction gives the checked generated Room corridors
and the native and cross-backend comorphisms over the typed entry
signature category. The two instances recover the existing public
Rooms and comparison maps. `rvsdg_memref_factors` identifies the
composed native-to-RVSDG-to-MemRef comorphism with the existing
native-to-MemRef comorphism. The shared interface is for this native
single-address Phi source profile.
[Coherence theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/CarriedAddress/Institution/Backend/Instances/Thms.lean)

```lean
import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Backend.Instances.Thms
```

A checked address swap preserves the translated result
`(0, [9, 9, 99])`. Identifying the two address ports restricts the
reduct image to coincident addresses, excluding a valuation that
distinguishes the two sides by their final heaps.
[Regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/CarriedAddress/Institution/Backend/Regression.lean)

#### Composing typed address bindings

`Activation.bindAddress` binds one leading activation address to a
typed captured port. Applying it twice binds two address operands in
the same ordered body. `bindAddress_comp` pushes capture reindexing
through each binding. The initialized heap passes through unchanged
at the boundary, and each selected address is in bounds.

`petri_comp_iff_memref_header` compares the emitted coloured activation
with the emitted MemRef header after the composed valuation pullback.
It observes the actual successor, exit word when present, and entire
post-store heap. With one wiring fixed for a whole loop,
`petri_completion_map_iff_memref` and
`petri_no_completion_map_iff_memref` transfer finite results and their
absence. Firing traces and CFG budgets remain separate witnesses.
[Typed activation and fixed-wiring theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Institution/Lowering/Backends/Activation/Thms.lean)

The two-address fixture instantiates each occurrence column at the
activation boundary. Swapping which cell receives each store returns
zero in both cases, with heaps `[9, 5, 99]` and `[5, 9, 99]`. Identifying
the captured ports erases the distinction and restricts the pulled-back
valuations to coincident addresses. The fixture also checks a finite
whole-loop return and absence of a finite return with fixed wiring.
[Activation regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/Institution/Lowering/Backends/Activation/Regression.lean)

For the existing single-address generated Rooms,
`Backend.observe_translate_reemit` combines typed re-emission with
cross-backend translation and compares the decoded partial result at
the reduct. Its regression uses the actual single-address switch across
feedback.
[Shared Room observation law](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/CarriedAddress/Institution/Backend/Thms.lean)

```lean
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Activation.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Backend.Instances.Thms
```

#### Whole-loop feedback with two address Phis

`TwoAddress.Graph` gives each lane a typed entry capture and a separate
feedback operand. A feedback operand can select either old lane or a
captured address. Both operands read the same pre-jump bank. Each
activation runs the existing ordered Load/Store body, tests its returned
word against a captured stop word, and carries the complete post-store
heap. Addresses are in bounds by type, and the two lanes may coincide.
[Typed source](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/TwoAddress/Defs.lean)

`TwoAddress.Petri.lower` emits one numbered θ with the two address
lanes and the heap in its carrier. `read_entryWires` checks the initial
frame. `lowerActivation_run` and `lowerActivation_finishes_iff` give the
exact tail tag, routed operands and heap of the numbered and coloured
child. `lower_run` relates a native allowance of `b` backedges to
`b + 1` numbered activations. `lower_finishes_iff` transfers the word and
every cell between native finite return and a coloured firing trace
from one entry marking. `no_finishes_iff` gives agreement on absence of
any finite completion. Firing traces have their own witnesses.
[Public theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/TwoAddress/Petri/Thms.lean)

```lean
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Petri.Thms
```

The regression composes two `bindAddress` bindings into a simultaneous
swap. It checks the packets `(0, 1) → (1, 0) → (0, 1)` and runs the
emitted graph with a budget of three activations. The word is zero and
the final heap is `[0, 0, 0, 42]`. Coincident entry addresses also return
zero and leave `[0, 5, 0, 42]`.
[Runnable regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/TwoAddress/Petri/Regression.lean)

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Petri.Regression
```

The same source lowers through `TwoAddress.MemRef.lower` to an ordered
typed CFG with entry, header, and exit blocks. The two header block
arguments are signless integers of width `cells.log2 + 1`. The checked
decoder recovers in-bounds MemRef indices before any memory effect.
Both feedback operands are read from the old header bank before the
conditional branch installs its successor frame. The emitted
`memref.load`, `memref.store`, and tail comparison reuse the existing
ordered activation. The initialized rank-one buffer lives in the shared
state and the invariant typed captures are supplied to the evaluator.
[Emitter](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/TwoAddress/MemRef/Defs.lean)

`decodeAddresses_eq_some` characterizes the admitted address frames.
`header_transition` identifies the actual feedback pair or exit word
and the entire post-store buffer. `run_eq_evalWithin` uses `b + 3`
blocks for a native allowance of `b` backedges (entry, the initial
header, the further headers, and exit). `returns_iff` and
`no_return_iff` compare all finite returns and their absence.
`petri_finishes_iff_runFuel` and `petri_no_finishes_iff_no_return`
compose these laws with coloured Petri using independent witnesses.
[MemRef theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/TwoAddress/MemRef/Thms.lean)

```lean
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.MemRef.Thms
```

The shared fixture returns with the same full buffers in both backends.
The double swap needs five CFG block steps, and the coincident pair
needs four. One fewer block yields no return in each case. A raw
out-of-bounds second operand is also refused by the emitted header.
[Runnable MemRef regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/TwoAddress/MemRef/Regression.lean)

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.MemRef.Regression
```

#### Two-address equations and termination

`TwoAddress.Institution.translate` puts the actual numbered θ lowerings
into the existing `RVSDG.NestedTheta.Institution.RuntimeObservation`
room as partial equations or termination sentences. At a fixed cell
count, its canonical runtime model admits exactly the typed input
tuples paired with complete initialized heaps. The shared heap and
tuple codecs supply this correspondence.
[Sentence and observation adapters](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/TwoAddress/Institution/Defs.lean)

`Sentence.Holds` fixes a typed valuation and quantifies over initial
heaps. `Sentence.HoldsAt` also quantifies over all typed valuations at
that cell count. `satisfaction` identifies the latter with satisfaction
in the existing numbered room and with the corresponding observations
of the emitted MemRef CFG and coloured Petri net. Equations compare
word and every final cell, and accept two absent finite observations.
A termination sentence requires some finite return for each entry,
with separate witnesses for each entry and backend. The comparison
uses the canonical memory runtime at this opcode alphabet.
[Public theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/TwoAddress/Institution/Thms.lean)

`runtimeObserve_eq_none_iff_native` identifies an absent observation
with absence of a finite return. It leaves infinite firing schedules
outside the observation. `MemRef.cfg_run_isSome` proves that the raw
CFG run from the emitted entry succeeds in the outer option at every
fuel. The inner option can be absent because that fuel did not reach
a return. The outer option can fail at a malformed raw header, as the
address-decoder regression illustrates.
[MemRef fault and fuel laws](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/TwoAddress/MemRef/Thms.lean)

The shared swap fixture compares the swapping and stationary graphs.
At coincident addresses their equations agree at every heap for that
valuation. At distinct addresses, the same returned word with a
different final cell refutes the equation at the chosen cell count.
The regression also accepts a universally terminating loop and
rejects one with a fixed continuing header at a concrete entry.
[Runnable regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/TwoAddress/Institution/Regression.lean)

```lean
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Thms
```

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Regression
```

#### Native and generated MemRef institutions for two addresses

`TwoAddress.Institution.inst` and `MemRefRoom.inst` use the existing
category of typed capture-port maps. A map from `P` to `Q` renames
captures in the ordered body and the entry and feedback operands. The
two old header lanes retain their positions under the lifted map.
Models pull back from `Q` to `P` by reading the renamed ports at the same
cell count. The native and generated corridors obey identity and
composition.
[Typed reindexing](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/TwoAddress/Institution/Reindex/Thms.lean)

`MemRefRoom.comparison` is the native-to-generated `Inst.CoHom`. Its
sentence action stores the emitted CFG family and the source needed
for re-emission. Its model action is the identity at each signature.
The generated room executes the stored CFG at the model's cell count
and valuation. Equations compare the returned word and every final
cell at every initialized buffer. Termination requires a finite
return for each such buffer.
[Comorphism and satisfaction](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/TwoAddress/Institution/MemRefRoom/Thms.lean)

`Sentence.numbered` uses the same source to translate into the existing
numbered runtime room. `GeneratedProgram.returns_iff_numbered` compares
whole results at the same entry valuation with independent finite
witnesses. `Sentence.numbered_satisfaction_at_model` compares the two
sentence forms at that valuation. The room-level
`Sentence.numbered_satisfaction` ranges over all valuations at a cell
count in the canonical runtime. After re-emission,
`Sentence.numbered_satisfaction_map` ranges over the reduct image of
those valuations. The comparison uses the fixed ordered runtime opcode
alphabet and its canonical model.

The regression uses a typed port identification. At a distinct-address
valuation, two generated programs return the same word and disagree
on cell 1. After re-emission identifies the two captured ports, the
equation holds in the generated room and its numbered translation
holds at the canonical model.
[Runnable regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/TwoAddress/Institution/MemRefRoom/Regression.lean)

```lean
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.MemRefRoom.Thms
```

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.MemRefRoom.Regression
```

#### Generated numbered institution for two addresses

`TwoAddress.Institution.RuntimeRoom.comparison` is an `Inst.CoHom` over
the existing typed capture-port category. Each sentence retains the
source and the emitted whole θ. A capture map re-emits from the
renamed source, and the model reduct pulls back the typed valuation
at the same cell count. `GeneratedProgram.observe_map` compares the
complete partial results at that reduct using `RuntimeObservation`
on the stored programs.
[Numbered institution](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/TwoAddress/Institution/RuntimeRoom/Thms.lean)

Models choose the canonical memory runtime at their cell count and fix
one typed capture valuation. Equations compare the returned word and
every cell over all initialized heaps. Termination requires a finite
return for each such heap. `Sentence.numbered` exposes the stored
programs in the existing numbered room. At its canonical runtime,
`Sentence.numbered_satisfaction_map` quantifies over the target
valuations pulled back by the capture map.

`toMemRefComparison` re-emits the same source as a MemRef sentence at
the same models. `comparison_factors` identifies the composed
native-to-numbered-to-MemRef comorphism with the direct MemRef one.
`Sentence.toMemRef_satisfaction_map` transfers both sentence forms at
the reduct. Complete finite observations retain their own execution
witnesses in each backend.
[MemRef coherence](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/TwoAddress/Institution/RuntimeRoom/MemRef/Thms.lean)

The regression rejects the distinct-address equation by cell 1,
then checks the same comparison after a noninjective port map
identifies the address captures. It checks the numbered room, the
existing runtime sentence, and the direct MemRef path.
[Runnable regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/TwoAddress/Institution/RuntimeRoom/Regression.lean)

```lean
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom.MemRef.Thms
```

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom.Regression
```

#### Coloured observation of the two-address θ

`TwoAddress.Institution.PetriRoom.comparison` uses the generated numbered
room's sentences, typed valuation models and capture maps. The
`GeneratedProgram.petriObserve` observer reads the stored whole θ through
coloured firing. The trace starts at the net's initial marking with
the canonical typed capture bank and complete initialized heap as root
colours. A finite completed trace witnesses the returned word and
every final cell.
[Coloured observer and comparison](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/TwoAddress/Institution/PetriRoom/Thms.lean)

`petriObserve_eq_numbered` identifies the entire partial value, with
independent firing and numbered evaluation witnesses.
`petriObserve_eq_none_iff` characterizes absence of any finite completed
trace. In the coloured room, an equation compares these partial values
at every initialized heap. A termination sentence requires some
completed trace at each initialized heap.

`petriObserve_map` compares the re-emitted observation with the source
observation at the typed reduct. `numbered_satisfaction_map` gives the
canonical numbered room's global comparison over the pulled-back target
valuations. The regression observes equal returned words with differing
cell 1 values, then checks the re-emitted equation after the two address
captures are identified through the numbered comparison.
[Runnable regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/TwoAddress/Institution/PetriRoom/Regression.lean)

```lean
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.PetriRoom.Thms
```

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.PetriRoom.Regression
```

### Equations for coloured Petri completion

`petriHolds` compares the two emitted graphs' finite completions for
every initial heap at the chosen typed model. Each result contains the
word and every final cell. If both graphs have no finite completion at
an initial heap, both partial observations are absent there.
`petri_satisfaction_iff_memref` and `petri_satisfaction` identify this
relation with MemRef and native equation satisfaction.
`petri_satisfaction_reindex` uses the native typed entry map and
valuation reduct.

The backend regression rejects equal words with different final cells.
It also compares two programs that both exhaust a zero-backedge
allowance. One returns after another activation, and the other has
no finite completion at that heap.
[Equation theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Institution/Lowering/Backends/Thms.lean) ·
[Regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/Institution/Lowering/Backends/Regression.lean)

Save this example to a Lean file and run `lake env lean <file>`. The
activation results list the selector, word, and both final cells. The
feedback and CFG results list the word and both final cells on return.
The final examples check a partial observation and an equation at that
typed valuation.

```lean
module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Feedback.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Feedback.Defs

open Silmaril.SSA.RVSDG (Tuple)
open Silmaril.SSA.SeaOfNodes.Memory (Address Heap ValueSort Val Word)
open Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution (Signature Model)
open Silmaril.SSA.SeaOfNodes.Memory.Loop (Graph)
open Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution (Equation)
open Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Institution (Holds observe observe_eq satisfaction)
open Silmaril.MLIR.MemRef (Buffer)
open Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef (runActivation runAfter)
open Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF renaming run → runCfg

private abbrev args : List ValueSort := [.address, .word]

private def graph : Graph args where
  body := .load (.latest 0) (.arg .head)
    (.store (.latest 0) (.arg .head) (.arg (.tail .head))
      (.ret (.latest 1) (.output 0 .head)))
  effects := rfl
  stop := .tail .head

private def input : Tuple (Val 2) args :=
  .cons (0 : Address 2) (.cons (7 : Word) .nil)

private def start (old : Word) : Buffer 2 :=
  ⟨fun i => if i = 0 then old else 99⟩

private def exampleResult (old : Word) : Nat × Nat × Nat × Nat :=
  let (.cons selector values, final) :=
    runActivation graph input (start old)
  (selector.down.val, (values.get .head : Word).toNat,
    (final.cell 0).toNat, (final.cell 1).toNat)

#eval exampleResult 7  -- (0, 7, 7, 99)
#eval exampleResult 8  -- (1, 8, 7, 99)

private def feedbackResult (count : Nat) (old : Word) : Option (Nat × Nat × Nat) :=
  (runAfter graph input count (start old)).map fun (word, final) =>
    (word.toNat, (final.cell 0).toNat, (final.cell 1).toNat)

#eval feedbackResult 0 7  -- some (7, 7, 99)
#eval feedbackResult 0 8  -- none
#eval feedbackResult 1 8  -- some (7, 7, 99)

private def cfgResult (budget : Nat) (old : Word) : Option (Nat × Nat × Nat) :=
  (runCfg graph input budget (start old)).map fun (word, final) =>
    (word.toNat, (final.cell 0).toNat, (final.cell 1).toNat)

#eval cfgResult 0 7  -- some (7, 7, 99)
#eval cfgResult 0 8  -- none
#eval cfgResult 1 8  -- some (7, 7, 99)
#eval cfgResult 2 8  -- some (7, 7, 99)

private def signature : Signature := ⟨args⟩
private def model : Model signature := ⟨2, input⟩

example : observe graph model (start 8).cell = Part.some (7, (start 7).cell) := by
  refine (observe_eq (P := signature) graph model (start 8).cell).trans ?_
  apply Part.eq_some_iff.mpr
  apply (graph.returns_iff_mem_denote input (start 8).cell 7 (start 7).cell).mp
  refine ⟨1, (graph.returnsAfter_iff_evalAfter input (start 8).cell 1 7 (start 7).cell).mpr ?_⟩
  cbv
  congr 2
  funext i
  by_cases atHead : i = 0 <;> simp [Heap.write, Function.update, atHead]

example (e : Equation signature) : Holds e model ↔ e.Holds model :=
  satisfaction e model
```
