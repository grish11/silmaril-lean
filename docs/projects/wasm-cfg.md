# Control-flow graphs of Wasm functions (`Silmaril.Wasm.Cfg`)

`Cfg.ofExpr`/`ofFunc` extracts the instruction-level CFG of a function body (structured control)
as a `Silmaril.Machine.Graph.Digraph`. This is the rooted-graph type whose dominators and dominator
trees `Silmaril.Automata.Graph` analyses, and which state machines use too.

## What is extracted

- One node per instruction occurrence, named by its path through nested bodies, plus the special
  nodes `exit` (0), `trap` (1), `raise` (2) and `invalid` (3).
- Edges follow the structured-control rules, with branch targets resolved syntactically by label
  depth:
  - `block`'s label is its continuation, and `loop`'s label is the loop itself;
  - `if` goes to both arms;
  - `br`, `br_if` and the `br_on_*` forms go to their label's target, and the conditional ones also
    go to the next instruction;
  - `br_table` goes to every listed target and to its default;
  - `return` and tail calls go to `exit`;
  - `unreachable` goes to `trap`;
  - `throw` goes to `raise`;
  - a missing label goes to `invalid`.

## Stated approximations

- **Exceptions.** An exception's handler is not resolved: `throw` goes to `raise`. `try_table`
  links to every catch target, which over-approximates.
- **Run-time traps.** Instructions that may trap at run time (division, memory, casts) and calls
  whose callee may trap or throw get no trap edge.
- **Calls.** Calls continue to the next instruction. The call graph is separate and not done yet;
  so is resolving `call_indirect` targets.

## Evidence

`Silmaril.Wasm.Cfg.Thms` checks the extractions of example functions in the kernel (exact edge
lists and dominators):

- `sum` of `Examples.Verified.prog`: a loop in a block. Its `br_if` is the immediate dominator of
  the block's exit.
- A `br_table` dispatcher: its targets are the continuations of the three blocks.
- `unreachable` / `throw` / `return` go to the special nodes.
- A missing label goes to `invalid`.
- The compiled Rust `enter` of `Examples.RustInst.door`.

**Not proved yet:** a general theorem relating `ofExpr` to an operational semantics of structured
control. That is the next milestone; the facts above are checked extractions, not a proof that the
extractor is correct.

## In the explorer

`silmaril/machines/wasm-cfg.toml` holds these CFGs as machine documents, written by
`ProjectSelfTest.WasmCfg.cfgDoc`. The `*_extracted` theorems prove in the kernel that each
document has exactly the extraction's nodes and edges.

The registry proves each document's immediate-dominator table. The explorer's machine page
(Machines → `silmaril.wasm.cfg.*`) shows the flat CFG and its Lean kernel-checked dominator tree.

## Roadmap: basic-block CFG relation

The instruction-level extractor above is a prototype. The target is a **relation** from a Wasm
function to a CFG whose nodes are basic blocks, with proofs that it is a function (existence and
uniqueness) and that the executable extractors realize it.

**Decisions so far:**

1. **Canonical partition** (`Silmaril.Wasm.Cfg.Block`, done).
   - *Terminators* are the structured instructions (`block`, `loop`, `if`, `try_table`), the
     branches (`br`, `br_if`, `br_table`, `br_on_*`), `return` and tail calls, `unreachable` and
     `throw`/`throw_ref`.
   - Calls are *simple*: their trap or throw exits are marked on the node, not made separate edges.
   - A segment is simple instructions followed by at most one terminator.
   - `IsSegmentation` is the relation: nonempty segments covering the sequence, where only the last
     may lack a terminator.
   - **Proved:** every sequence has exactly one segmentation (`existsUnique_segmentation`), and
     `segment` computes it.
   - A block's identity is (sequence path, position in the segmentation).
2. **Nested sequences and edges** (`Silmaril.Wasm.Cfg.BlockTree`, `Silmaril.Wasm.Cfg.BlockCfg`,
   done except the benchmark).
   - Nodes are the segments of every sequence of the body tree (bodies of `block`, `loop`, `if`
     arms and `try_table`). A `BlockId` is a sequence path of `(segment, arm)` steps plus a
     position. `lookup body b` names the block declaratively, through the canonical segmentations.
     **Proved:** `blocks` lists exactly the graph of `lookup` (`mem_blocks`).
   - Edges are given declaratively from `lookup` (`succOf`, `Edge`):
     - `entry` gives the block at a position, or else the sequence's continuation.
     - A nested sequence continues at its parent's next position; the body continues to `exit`.
     - `loop` labels go to the loop body's entry; other labels go to the continuation.
     - Branches resolve by depth; the outermost label is `exit`.
     - `try_table` has an edge to each catch label, resolved outside it.
   - Special nodes stay explicit: `exit`, `trap`, `raise`, `invalid`.
   - **Proved:**
     - the one-pass builder `blockCfg` realizes `Edge` (`blockCfg_eq`, `edge_iff`);
     - each block has exactly one successor list (`existsUnique_succ`);
     - block identities are distinct (`blocks_ids_nodup`, `blockCfg_ids_nodup`).
   - Kernel-checked examples: `sum_blockCfg`, `dispatch_br_table_edges` (`decide +kernel`, a
     few seconds).
   - **Scope: syntactic and incomplete.** `Edge` is the structured-control reading of the
     instruction tree. It is not derived from, or proved against, the Core 3.0 semantics; no
     theorem says that executions follow it. That correspondence is the operational bridge
     (behavioral equivalence, item 5 below).
   - **Effect marks and effect edges** (`blockEffects`, `effectSucc`, `EffectEdge`). These are
     syntactic and conservative ("may"). They keep the control edges from looking complete
     where other instructions may leave the block:
     - `mayTrap`: division and remainder, `trunc`, memory and table accesses, null and cast
       checks, array operations. Effect edge to `trap`.
     - `call`: direct, indirect and reference calls, including tail calls. Effect edges to
       `trap` and `raise`, because the callee may trap, raise or not return.
     - `unresolvedHandler`: a block inside a `try_table` body that calls or throws. Its exception
       may be caught by an enclosing `try_table`, and the graph does not resolve which handler.
       Its `throw` flow edge still goes to `raise`.
     - Kernel-checked example: `guarded_effects`, `guarded_effect_edges`.
   - Kernel against runtime evaluation: measured, see *Benchmark* below.
   - On the explorer: `silmaril/machines/wasm-block-cfg.toml` holds the block CFGs of `sum`,
     `dispatch`, `specials` and the Rust door's `enter`, as machine documents
     (`silmaril.wasm.blockcfg.*`), each with its kernel-checked dominator table. There is also
     `guarded`, which has effects. Edges are labelled `flow` or `effect`, and blocks carry their
     effect marks.
   - Each document's description, and the explorer's dominator caption, say the graph is
     syntactic and incomplete: the dominator theorem is a fact about the drawn graph, not about
     execution.
     `ProjectSelfTest.WasmBlockCfg.*_blocks` proves that each document has exactly the builder's
     nodes, edges and entry, by node index. The instruction-level documents
     (`silmaril.wasm.cfg.*`) stay alongside for comparison.
3. **Node interfaces**, relative to a fixed module environment.
   - **The environment is not part of a body.** Every interface is under a `Validation.Context`
     built as `checkModule?` builds it (`moduleCtx`: types, funcs, globals, tables, mems, tags,
     elems, datas). A body never carries it.
   - **Body interface:** `(params, locals, results)` under that context, as in
     `Context.funcBody`.
   - **Block interface:** the label stack (`withLabel` along the block's path), the local
     initialisation state, and the operand stack in and out of the block's own frame.
   - This is shared with the abstract typed-body work (`docs/projects/component-semantics.md`),
     so there is one notion of interface.
   - **Local values are not in the context.** The context holds the local *types* and their
     initialisation state. Local values belong to the activation frame of a run, apart from the
     module store, as the abstract typed-body interface also has it.
   - **Done** (`Silmaril.Wasm.Cfg.BlockTyping`): `bodyIfaces C body` records each block's
     interface: static context, instructions, stack in → out, and local initialisations.
     `bodyIfaces_typed` proves that every recorded interface is an `Instrs_ok` derivation.
     `bodyIfaces_lookup` proves that a recorded interface's instructions are the segment
     `lookup` names for its identity. The explorer shows these interfaces for all 3,125 blocks.
   - `bodyIfaces_complete` proves that, when the validator's expression check accepts the body
     (as `funcCheck` runs it), every block gets an interface. So a validated body has one proved
     typed interface per block.
   - **Open:** a statement about runs.
   - The trap/throw effect marks and referenced indices stay syntactic.
4. **Bytes**, valid serializer profile only (`encodeModule?`).
   - The encoded object is (locals, body). It is an *encoding* object only: semantically, a
     function is (type index, body) under the module's context, and the explorer's function pages
     are (module, index).
   - Its *body encoding* is the locals vector, then the expression, then `end` (`0x0b`).
   - Its *code entry* is the body encoding with a u32 size prefix.
   - The code section lists entries in the order of defined functions; module function index `k`
     is `#imports + defined index`.
   - A block's bytes are its simple instructions followed by its terminator's header (opcode and
     block type). The nested sequences' bytes belong to their own blocks; the `else` and `end`
     delimiters are attributed to the end of their sequence.
   - To prove: the code entry of defined function `k` occurs in the module's bytes at the offset the
     encoder places it.
5. **Equivalences.**
   - Graph equivalence is an isomorphism of block CFGs that preserves block contents.
   - Dominator-tree equivalence goes through the exact dominator tree, which is unique on reachable
     nodes (`Graph.exact_unique`). So it does not depend on choosing a tree, unlike sound or region
     trees.
   - The operational bridge comes first: a block step relation stated through Core 3.0 `Steps`,
     with a simulation onto CFG paths, starting with the fragment without calls.
   - Behavioral equivalence (function to CFG injective up to equivalence: semantics preserved and
     reflected) needs the abstract environment and trace semantics owned by the Wasm games/traces
     work. This development reuses that, and does not port a second semantics.

## Benchmark: kernel against runtime evaluation of `blockCfg`

Method:
- Each case is one file importing `Silmaril.Wasm.Cfg.BlockCfg.Thms`, run with `lake env lean`.
- *Runtime* is `#eval (blockCfg body).length`; *kernel* is
  `theorem : (blockCfg body).length = n := by decide +kernel`.
- Wall time minus the 3.0 s import-only baseline. One run per case on a 2-core container,
  toolchain `nightly-2026-11-05`. Run-to-run variation of the whole process was about 0.3 s, so
  smaller differences are not resolved.

Bodies:
- `synth d` nests `d` loops, each level `local.get 0; br_if 1; loop … br 0 end; nop`
  (`3d + 1` blocks, nesting depth `d`).
- `flat w` is `w` copies of `local.get 0; br_if 0` at the top level (`w` blocks, depth 0).

| body | blocks | runtime | kernel |
|------|-------:|--------:|-------:|
| `synth 10` | 31 | not resolved | not resolved |
| `synth 50` | 151 | not resolved | not resolved |
| `synth 200` | 601 | not resolved | 2.3 s |
| `synth 400` | 1201 | not resolved | 9.7 s |
| `synth 800` | 2401 | not resolved | 57 s |
| `flat 1000` | 1000 | not resolved | 0.4 s (near resolution) |
| `flat 4000` | 4000 | not resolved | 1.7 s |

Reading (these single runs only; no general complexity claim):
- *Runtime:* every `#eval` run finished within the baseline's run-to-run variation. That is a
  measurement-resolution statement about these cases, not a time bound.
- *Kernel, nesting:* checking time is sensitive to nesting depth. Doubling the depth from 200 to
  400 multiplied it by about 4.2 (2.3 s to 9.7 s), and from 400 to 800 by about 5.9 (9.7 s to
  57 s). Three points from one run each do not fix a growth rate.
- *Kernel, flat:* for the flat family, 4000 blocks took 1.7 s.
- Each nested block's identity carries its full path, which is a plausible source of the depth
  sensitivity; this was not profiled.
- These two synthetic families say nothing measured about other function shapes.

## Plan: execution follows the CFG (operational bridge)

**Goal.** Theorems about Core 3.0 runs of a function body, which remove the "syntactic,
incomplete" caveat. Nothing here is assumed of a grouping of the graph, such as a dominator
or region tree. Every semantic claim is a theorem against `Silmaril.Wasm.Execution.Core.Step`.

**Audit of what can be reused:**
- The target is the block CFG over `Instr` (`Cfg.Edge`, `lookup`, `entry`/`cont`/`labels`).
- The proof tools are `Execution.Core.Sim.Context` (`Step.split_head`, `Exit`/`ExitShape`,
  context lifting) and the `Logic.Core` decomposition (`labelPost`, `blockPost`, `loopPost`).
  Both work on `Instr` against `Step`.
- Three developments do not fit:
  - the native interpreter (`Interp`, `native_adequacy`) and the structured fragment
    (`SSA.Fragment`, `behaviours_eq_run`) work on `BExpr` or the fragment `Expr`, are
    integer-only with no exceptions, and characterise only final outcomes, not the blocks a
    run passes;
  - the abstract `BodyM`/`IterOps` layer has no link to Core yet.

**Scope: coverage is not equivalence.** A forward simulation (every Core step from a
position moves along a CFG edge) shows that the graph *covers* execution: every run projects
to a graph path. It does not give equality with the function's behaviours, for two reasons:
- **Infeasible paths.** The graph's `if`, `br_if` and `br_table` edges ignore the data
  conditions, so many graph paths are not runs.
- **Conservative marks.** The effect marks and edges are conservative, so they include
  outcomes no run reaches.

Behavioural equivalence needs more:
- an *executable* CFG semantics: typed blocks carrying values, locals and the store, whose
  branches read the data;
- a reverse simulation, or adequacy (every run of that semantics is a Core run);
- matching treatment of initialisation, termination and divergence.

The plain graph stays an over-approximation, and claims about it say so.

**Milestones**, each a bounded PR with no `sorry` on `main`:
1. **Position invariant.** `At body pos cfg` relates a reachable configuration of the body
   (nested `LABEL_n{cont}` contexts around `val* rest`) to a position
   `(BlockId, offset, value stack)`. Every `cont`/`rest` is a suffix of a nested sequence of
   the body, and a loop continuation re-expands to its `loop`. Proved: the invocation
   configuration is `At` the entry.
2. **Straight-line steps.** A Core step from an `At` configuration whose next instruction is
   not a terminator is `At` the next offset of the same block. A trapping step is a `trap`
   effect edge of that block.
3. **Control steps.** The steps of the terminators (`block`/`loop`/`if` entry, `br`,
   `br_if`, `br_table`, `br_on_*`, `return`, label exit, `unreachable`) move from `b` to a
   position at the entry of some `t` with `Edge body b t`, or to `exit`/`trap`.
   *Done so far* (positions in `Cfg.Exec`, against `Step`): entering `block`, `loop`,
   `try_table` and the chosen `if` arm, and falling out of a `block`/`loop`/`if` arm
   (`resid_at_block_step` … `resid_inArm_done_step`). These use the shared Core inversions in
   `Execution.Core.Inversion` (stuck codes, `call`/`call_ref`, `LabelExit`/`HandlerExit`/
   `FrameExit`). Still to do: steps inside a label (lifting a body step through
   `ctxt-label`), branches and their bubbling, `try_table` fall-through and catches, and the
   projection of positions to `Cfg.Edge`.
4. **Exceptions as control** (#230): a `throw`, or a raise out of a call, resolves to the
   enclosing `try_table` catch target or leaves the function. The CFG gets resolved exception
   edges for this, proved against the `HANDLER` rules. This replaces `handler-unresolved` and
   the call → `raise` effect edge. Trap and raise stay distinct.
5. **Path theorem.** Every finite run prefix, and every infinite run, of a call-free body
   projects to an edge path from `cfgEntry`. Divergence is an infinite path.
6. **Precise effects.** Each `trap` edge is justified by a step that traps (no generic "may").
   The converse, that every such edge is reachable, is not claimed unless proved.
7. **Executable block semantics and adequacy.** A typed block semantics (values, locals,
   store; branches read the data) and the reverse simulation. Only with both may equivalence
   with `behaviours` be claimed. For the structured native fragment, equality of its runs with
   the fragment's `Run` then gives Core 3.0 call-equivalence (`callEquiv_of_run_iff`).
   *First slice done* (`Cfg.Region`): a compositional big-step region semantics `Run` on Core
   runtime code (values, non-control instructions, `block`/`loop`/`if`/`br`/`br_if`/`return`,
   `LABEL`, `TRAP`) with outcomes `normal`/`br`/`ret`/`trap`. It is adequate for Core 3.0 in
   both directions, for every profile and host, on terminating runs: `run_adequate`,
   `body_adequate`, and `frame_adequate` for function frames. Sequencing is
   `run_append_iff`. Divergence: `RunDiv` (structural greatest fixed point) with `div_iff`
   (`RunDiv ↔ Core Diverges` on the fragment), using `atomTerm` (every non-control instruction's
   reduction is strongly normalising, by expansion level and bulk counts). `br_table` and
   `br_on_*` are in the fragment (`BrStep`), and so are exceptions (`throw`, `throw_ref`,
   `try_table`, `HANDLER`, clause resolution `Catches`; outcome `throw a`). Calls inside bodies remain.
8. **Calls**, through an explicit call interface: a call node whose callee behaviour is a
   parameter (a `FRAME` run of the callee), first for direct calls.

9. **Native trees ↔ region semantics** (`Cfg.Bridge`, `Cfg.BridgeBwd`). The native evaluator
   on folded trees (`CallX.EvalOX`, oracle `C`) against `Region.RunC` of their lowering, with the
   same oracle; `ResOut` relates the ends (pending tail calls answered at the frame, branch and
   return values carrying the enclosing labels' values in the region).
   - **Forward, done** (#492): `bridge_fwd` (typed `EvalOXT`, `chkE tExt`-checked, oracle sound
     for the tail-aware check), `bridge_fwd_closedX` (the typed closed extended oracle, no oracle
     hypothesis).
   - **Backward, flat case, done**: `flat_bwd` (deterministic profile `SingleThreaded.profile o`,
     any host and oracle): a region run of a checked, typed flat instruction other than a call is
     its `evalFlat` result, from HostEval's `flat_complete` (#496).
   - **Backward, trees without extended calls, done**: `bridge_bwd` (deterministic profile, no
     host, an oracle sound for the tail-aware check that keeps typing) and `bridge_bwd_closedX`
     (the typed closed extended oracle, no oracle hypothesis): a region run of the lowering of
     typed trees with no `call_indirect`, `call_ref` or tail call (`CallX.xFreeL`; direct calls
     included) is a native `EvalOX` run with the same oracle, ending as `ResOut` says. Loops are
     by induction on their region run (`loop_aux`), re-entering at each branch back.
   - **Backward, trees without tail calls, done**: `bridge_bwd_tailFree` and
     `bridge_bwd_tailFree_closedX` add `call_indirect` and `call_ref` (resolved as the native
     evaluator resolves them, answered by the same oracle entry); `bridge_bwd` is its
     `xFreeL` case.
   - **Backward, every outcome but a pending tail call, done**: `bridge_bwd_nonTail` and
     `bridge_bwd_nonTail_closedX` cover every typed tree, tail calls included, when the region
     outcome is not `Out.tail`: `return_call_ref` on null and `return_call_indirect` without a
     callee trap natively. `return_call_indirect`'s `table.get; ref.cast` Core runs are forced at
     the deterministic profile without host (unique host-free normal forms,
     `BridgeBwdRci.run_rci_inv`).
   - **Backward, pending tail calls, done**: `bridge_bwd_tail` (and `_closedX`): a region run
     ending in `Out.tail W a c` corresponds, for **every** oracle answer to that call
     (`ResOut … (.tail W a c) r`), to a native run to `r`; the callee's parameters are on `W`
     (typing at the call site), so enclosing labels do not change the arguments.
     `bridge_bwd_answered` (and `_closedX`) is the existence form: if the outcome is not a
     pending tail call, or the oracle answers it, the region run is a native run with the same
     oracle, ending as `ResOut` says. This is the draft #494's `Task.bwd` with its honest
     hypothesis: without an answer to a pending tail call there is no native result. The draft's
     `sorry`s are replaced and it is not merged.
   - **CFG corollaries, done** (`Cfg.BridgeCfg`): `machine_native` (a machine run from
     `cfgEntry` of typed trees without tail calls to a sink is a native run with the same
     oracle, the sink's `EndsC` and the native result related by `ResOut`) and `native_machine`
     (a typed checked native run from the empty stack is a machine run from `cfgEntry` to a sink
     completing its region outcome, unless that outcome is a branch out of the body; pending tail
     calls are completed by the oracle answer `ResOut` carries), with the `closedXOk` instances
     `machine_native_closedX`, `native_machine_closedX` (no oracle hypothesis). These are about the
     block-CFG machine as an executable semantics; the plain graph stays an over-approximation.

10. **Branches to the function label (bug in the block-CFG machine; fixed).** A function
    body runs under its function's label (Core `FRAME_n{} (LABEL_n{} body)`), so a branch whose
    depth is the body's nesting depth returns; the native store check accepts it (labels
    `[rs.length]`) and the extracted CFG resolves it to `exit` (`labels body [] = [.exit]`). The
    machine's branch rules (`br`, `brIfTaken`, `brDataTaken`) need a label frame for the target,
    and the function label has none, so the machine is stuck exactly where the CFG has an `exit`
    edge; this is why `run_complete_initialC` excludes `br` outcomes.
    - **Regression fixtures, done** (`Cfg.ExampleBrOut`): the validated module `brOutMod`
      (`brOutMod_valid`) with a top-level `br 0`, a taken and an untaken `br_if`, a `br_table`
      to the function label from inside a block, and two results; Core returns their results
      under the function label (`core0` … `core4`), while the machine is stuck
      (`machine_stuck0/1/4`, `machine_no_sink0/1/4`, `machine_enter3` then `machine_stuck3`).
    - **Fix, done (machine transitions and soundness):** `MStepC.brOut`, `brIfOut`,
      `brDataOut` step from a block whose terminator branches to label index `ls.length` (the
      function boundary; deeper labels stay invalid) to `exit` with the block's values, as
      `return` does; `Ends` at `exit` adds `∃ W, o = .br 0 (W ++ stk)`. Every case analysis over
      `MStepC` is extended: soundness (`wrap_brOut`, `brOut_sound`, `brIfOut_sound`,
      `brDataOut_sound` in `mstep_sound`), the CFG edge (`resolveT_out`: the function label
      resolves to `exit`, so each new step is an `Edge` to `exit` in `mstep_edge`), and the Core
      simulation (`msim`: the new steps go to a sink). Divergence results are unaffected: the
      new steps end at a sink. The fixtures are restated as machine steps to `exit` with Core's
      results (`machine_exit0/1/3/4`).
    - **Completeness, done:** `run_complete_initial_outC`: every `RunC` run of the body that
      does not end in a pending tail call or in a branch past the function label is a machine run
      from `cfgEntry` to a sink, ending as `Ends` says; a branch to the function label reaches
      `exit`. The completeness induction's `Reach` asks, at a branch to label `ls.length`, for a
      run to `exit` (established by the new rules, carried outward through labels and handlers
      like `return`). `run_complete_initialC` (no branch outcome) is kept as a corollary.
    - **The same bug for `try_table`, fixed:** a catch clause whose label is the function label
      (`j + 1 + l = ls.length`) had no transition either (`catch_`/`bodyCatch` need a frame for
      the target). `MStepC.catchOut`/`bodyCatchOut` go to `exit` with the handler's outer values
      under the caught ones; soundness (`throw_catch_out`, `catchOut_sound`,
      `bodyCatchOut_sound`), the catch edge (`catch_edge` at index `ls.length` is `exit`), the
      Core simulation and completeness (`Reach` for a throw also asks for these catches) are
      extended.
    - `native_machine` now excludes only branches past the function label.

11. **A defined function's CFG execution against its Core invocation** (`Cfg.Function`).
    Fragment, stated explicitly: a typed invocation (`StoreOk`, `InvokeOk`) of a Wasm function in
    a store of Wasm functions with function types (`WasmFuncsT`) passing the tail-aware check
    (`StoreChkE tExt`: every call form, no `throw` or `try_table`), the deterministic profile, no
    host (closed: no observable call log). The machine runs the function's body in its call frame
    with calls answered by the typed closed extended oracle `CX closedCallX`.
    - **Finite runs, both directions, done:** `machine_core` (a machine run from the CFG entry to a
      sink is a native body run whose flow is a closed outcome of the invocation, and Core runs
      the invocation to the matching values or trap in the same final store) and `core_machine`
      (a stopping Core run of the invocation is terminal, a closed outcome, and the body's native
      run to it is a machine run from the CFG entry to a sink ending as that run; branches past
      the function label are ruled out by the body check).
    - **Callee divergence of every call form, soundness side:** `Region.DivFC` and the machine's
      `BodyCallDiv` admit a `call_indirect` resolved by `CallRes.IndRes` to a function and a
      `call_ref` of a function reference, answered by `C` or diverging inside the callee (`D`), next
      to direct calls. `div_soundC`, `bodyCallDiv_core` and `mdivC_core_initial` cover them under the
      same hypotheses (`CallSoundA`, `DivCallSound`, both stated for every `call_ref` form). A null
      table entry, null reference or failed cast traps (`RunC.callIndRes`, `RunC.callRefNull`) and
      has no divergence constructor.
    - **Callee divergence of every call form, completeness side:** `FragC` now has `call_indirect`
      and `call_ref`. `GuardedCalls` guards every `call_ref` of a function reference the run
      reaches, and a direct call's guard follows in one step (`guarded_call`). Finite completeness
      (`completeC`, `run_completeC`) rebuilds `call_indirect` from its Core unfolding
      `table.get; ref.cast; call_ref` (`callInd_back`, via the profile-generic inversions in
      `Proofs/Wasm/Cfg/IndSteps.lean`), and answers `call_ref` of a function by `callRef_incl`.
      Divergence completeness (`div_completeC`, hence `core_div_initialC`, `core_div_closed` and
      `mdivC_iff_core_closed_typed`) has `div_callInd`/`div_callRef`: the call diverges in the
      callee (`D`), or is answered with values and the continuation diverges. An unresolved index
      or null reference traps and never diverges. New Core inversions: `Step.callRef_top_inv(_seq)`
      and `Step.callIndirect_vals_inv_seq`. **Open:** completeness of divergence through a tail
      callee (`FragC` has no `return_call*`), a `call_indirect` fixture (needs a store with a
      table), and the function-level corollary via `invoke_diverges_iff_funDivX`.
    - **`call_ref` fixtures (`Wasm/Cfg/ExampleRef`):** `ref_machine_div`: in the frame of the
      validated self-call of `recMod`, `ref.func x; call_ref y` has no infinite machine run, yet
      `MDivC` with `closedCallOk`/`closedDiv` holds through `BodyCallDivRef`, and Core 3.0 diverges.
      `null_machine_trap`, `null_not_diverges`, `null_not_mdivC`: `ref.null; call_ref` moves to the
      `trap` sink in one step, and never diverges.
    - **Divergence through tail callees, soundness side:** `MDivT` is `MDivC` or a finite run to a
      block ending in a tail call of a callee `D` names (`TailCallDiv`, read as `MStepC.tail` reads
      it, with no answer). `mdivT_frame_initial` (and `mdivT_frame_closed`): from the CFG entry it
      is Core 3.0 divergence of the function's frame `FRAME_n{fi} (LABEL_n{} body)` in any outer
      frame. The tail call replaces the frame (`return_call_ref-frame-addr`, `frame_tail_div`), so
      the body's pending code and handlers are bypassed. Fixture `Wasm/Cfg/ExampleTail`:
      `block (return_call x); unreachable` in the frame of `recMod`'s self-call (`tail_machine_div`).
      **Converse (Core route, step 2):** `frame_div_complete`: a diverging Core frame either
      diverges inside, which is body divergence through the function label (`MDivC` by
      `core_div_initialC`; a label exit stops outside any frame), or is left; every frame exit stops
      except a tail call of a function (`return_call_ref-frame-addr`), whose call diverges: the body
      runs to the pending tail call (`run_completeC`), the machine reaches its block without an
      oracle answer (`run_complete_tail_block`, via `Reach`'s tail clause, now the block itself:
      `TailAt`), and `D` names the callee (`DivCallComplete`, guard by `Region.TailGuarded`).
      `mdivT_iff_frame` combines both directions. 
    - **Function-level divergence, both directions (Core route, step 3):**
      `Function.invoke_diverges_iff_mdivT`: on the fragment (typed invocation, `WasmFuncsT`,
      `StoreChkE tExt`, deterministic profile, no host), Core divergence of `invoke s a vs` is
      exactly `MDivT` with `CX closedCallX` and `calleeDivX o` on the body in the call frame.
      `Function.funDivX_iff_mdivT`: with `invoke_diverges_iff_funDivX`, so is native `FunDivX`.
      No hypothesis beyond the fragment: every instruction is in `FragC` (`fragIB_all`); the
      oracle is complete on the fragment (`callCompleteG_cx`, from `invoke_closedX_adequacy` and
      call transport), `calleeDivX` is (`divCallComplete_cx`), and the guards at calls and pending
      tail calls and the placement of pending tails come from typing of the entered frame
      (`guardedCalls_cx`, `tailGuarded_cx`, `tailsOk_of_typed`). Not claimed: hosts, exceptions
      (`tExt` rejects `throw`/`try_table`; no host alone does not exclude them), the
      store-retaining session view. Fixtures (`Wasm/Cfg/ExampleFunDiv`, a validated
      `tExt`-checked module): `fd_recursive`: functions recursing through `call_indirect`,
      `call_ref` and `return_call` diverge natively (`FunDivX`, by coinduction), in Core 3.0 and as
      `MDivT`; `fd_trap`: a `return_call_indirect` through a null slot and a `call_ref` on null
      trap (closed outcomes), so none of the three holds.
    - **Host-free function-list preservation** (`Wasm/Cfg/Restrict`): without a host, a region or
      machine run keeps the store's whole function list `F` (instances with types, modules and
      code), so every call and every `F`-only check (`StoreChkE`) sees `F`. Oracles agreeing on
      stores with `F` give the same runs, steps, infinite runs, `MDivC` and `MDivT`
      (`runC_funcs` … `mdivT_funcs`). Host-free only: nothing is claimed for host-mutated stores.
    - **Function-level divergence, soundness side:** `Function.invoke_diverges_of_mdivT`: on the
      fragment, `MDivT` with `CX closedCallX` and `calleeDivX o` (typed `tExt` callees whose
      invocation diverges) is Core divergence of `invoke s a vs`. With `F = s.funcs`, `CX
      closedCallX` answers as the Core-sound `closedXOk` (`cx_closedXOk`); the invocation steps to
      the function's frame (`call_ref-func`), which diverges by `mdivT_frame_initial`. **Open:**
      the converse, by the Core route (Core divergence ⇒ `MDivT`, reusing region completeness;
      `FunDivX` then by `invoke_diverges_iff_funDivX`).
    - **Tail calls in the fragment with calls (Core route, step 1):** `FragC` now has `return_call`,
      `return_call_indirect`, `return_call_ref` (and the runtime `return_call_ref` of a type).
      Core's `return_call_ref-label`/`-handler` moves all of a label's values out with the call, so
      on untyped code the reference may come from outside the label (`ref.func a; block
      (return_call_ref y)`), where the region semantics has no run: completeness with tail calls
      needs the typing fact that it does not (`TailWF`, along the run `TailsOk`; from typing,
      `tailsOk_of_typed`, via `retRef_ref_of_typed`). With it, `run_completeC` and `div_completeC`
      cover tail calls: a tail call ends the region in a pending tail call (`labelTail`,
      `handlerTail`, … through labels and handlers, which do not catch it), and a body never
      diverges at a pending tail call, which is stuck outside a frame. Divergence of the tail
      callee is frame divergence (`MDivT`), not body divergence. No EH coverage changes.
    - **Exit states carry the whole frame stack (semantic correction).** The machine's exits by
      `return`, a branch to the function label (`br`, taken `br_if`, `br_table`/`br_on_*`) and a
      caught exception branching to it (`catchOut`, `bodyCatchOut`) kept only the innermost
      block's stack, dropping the label frames' outer values; `Ends` at `exit` allowed any `W`
      below it. They now keep the whole stack Core unwinds, `brVals` (outer values under the
      block's; for a catch, the caught values over the handler's outer values, then the frames its
      branch leaves), and `Ends` at `exit` is exact (`o = .normal`/`.ret`/`.br 0` of the stack).
      Fall-through (via `popL`) and answered tail calls (frame replacement) were already exact and
      are unchanged; branches past the function label stay invalid. Soundness (`ret_sound`,
      `brOut_sound`, …, exact), completeness (`Reach`'s `br`/`ret`/catch clauses) and every
      downstream result were updated. Fixtures `Wasm/Cfg/ExampleExitStack`: nested `return`,
      `br`, `br_if` (taken, not taken) and `br_table` with an outer value, two results, against
      Core; an invalid body whose `return` reaches below its block (`machine_loss`, `core_loss`),
      on which the old exit lost a value (no general untyped claim).
    - **(b), host-free milestone: the CFG session is the instance session** (`Wasm/Cfg/Session`).
      Target: the canonical `DStrategy` `instSession I P s = StratSession.threadS (instTripleS I
      P) s` (`Abstract.InstSession`), hence the instance part of `core3SemD`, on an explicit
      typed fragment. Not "define the CFG object by Core and conclude `rfl`".
      1. **The CFG triple** `cfgTripleS I o`, operational: `cfgFinS` is machine runs (`MStepC`,
         oracle `CX closedCallX`) of the export's body in its call frame to a sink, the answer
         read off the sink state (`sinkResult`: the top `rs.length` values of the exit stack, the
         whole frame stack since the exit fix; `trap` keeping its store), and machine frame
         divergence `MDivT` with `calleeDivX o`; empty logs. It is **oracle-backed**: callees
         are answered by the native closed extended semantics `CX closedCallX`, not by recursive
         CFG machines. A self-contained recursive CFG closure would discharge the oracle later
         and is not claimed.
      2. **The fragment** `HFOk I s`: no imports, `I.WellFormed s`, only Wasm functions with
         function types (`WasmFuncsT`), `StoreChkE tExt`, at `profile o`. Preserved at every
         reachable store (`hfOk_of_reach`: the function list never changes host-free,
         `wellFormed_after_run`). Exceptions are excluded by `tExt`, separately from hosts; the
         proof derives that a closed outcome of a checked invocation is never a throw.
      3. **Equality**, both directions per activation (`instFinS_eq`): returning activations by
         NodeBridge `ret_iff` (empty logs) and `Function.core_machine`/`machine_core`, the sink
         reading matched against Core's result (`sink_cases`; values are typed, so the exit
         stack holds the results); divergent ones by `div_iff` and
         `invoke_diverges_iff_mdivT`. With empty `satP` and productive components (no import
         operations), `threadS_congr` gives `cfgSession_eq_instSession`; then `spull_cfgSession`
         (the finite plays are `I.strategy`) and `core3SemD_eq_cfgSessions`: `core3SemD
         (profile o)` interprets every numeric instance in the fragment at its instantiation
         store by its CFG session (and the others by their instance sessions).
      4. **No imports is not no infinite plays**: no imports removes import callouts, call logs
         and within-call productive host interaction, not infinite session plays.
         `mem_inf_cfgSession`: the infinite plays are exactly those of the coherent infinite
         sequences of export rounds (`InfRounds`, via `mem_inf_instSession`/`StoreDet` and
         `infRounds_iff`), trap-resume rounds included; `infRounds_repeat`. Fixtures
         (`Wasm/Cfg/ExampleSession`, a validated two-export module, no imports): `ses_hfOk`;
         export `0` traps and export `1` answers `7` on the machine; `trap_forever` and
         `alt_forever` (trap, answer, trap, …) are infinite plays of the CFG session and of the
         instance session.
         **`cfgSessions` is compatibility, not coverage**: outside `HFOk` it falls back to the
         Core 3.0 instance session; no CFG semantics of general modules or components is
         claimed without the domain hypothesis.
    - **The domain, checked, and components on it** (`Wasm/Cfg/SessionCheck`):
      - `hfOk_of_check`: for a validated module without imports, instantiated into the empty
        store, an instance passing the executable check `hfCheck` is in `HFOk`.
        - `hfCheck` uses existing checkers: `storeChkEB tExt`, a Wasm-function check, and export
          types via `expand?`.
        - Store typing comes from validation and instantiation.
      - `denUD_congrIn`: a denotation depends only on the core instances a component uses
        (`CompIn`).
      - `denUD_core3SemD_eq_cfgSession` and `denD_…`: when every core instance of a component
        is in `HFOk`, its Core 3.0 denotation is the one with CFG sessions. There is no
        fallback, and nothing is claimed outside the domain.
      - Regression: `ExampleSession.ses_hfOk_checked`.
    - **Catch exits (#866 regression)** (`Wasm/Cfg/ExampleCatchExit`, a validated module with a
      tag `[i32 i32] → []`): a caught exception branching to the function label exits with the
      whole frame stack: `machine_catch` (`1, 3, 4`: the `try_table`'s outer value under the
      payload) and `machine_catchNest` (`1, 2, 3, 4`, through an enclosing block), against Core
      returning the payload `3, 4` (`core_catch`, `core_catchNest`); the tag hypotheses hold at
      the module's instance (`catch_tag`). Exit state only: no exception coverage at the function
      or session level.
    - **Not implemented (ledger)**, in order:
      1. **Hosts**: imports in the CFG session: pending import calls and logs, productive
         within-call host interaction, host answers keeping or changing the store, and exceptions
         raised by host answers. Route H1–H3 below.
      2. **XP/EH**: exceptions in the session fragment (`throw`, `try_table`, handler matching,
         tail calls bypassing handlers, uncaught exceptions as `Answer.throw`), trap stores
         preserved. Covered by the same route: `EvalLXPS` has the exception rules.
      3. **Discharging the oracle**: callees run by the CFG machine through a recursive closure
         (H3), callee divergence included. Until H3 lands every CFG statement is oracle-backed.
      4. Untyped stores and instructions outside the checked fragments: unsupported, excluded by
         hypotheses.
    - **Route for hosts, XP/EH and the oracle (H1–H3, coordinator-approved).** The CFG machine
      `MStepC` is unlabelled: simple steps are Core `Steps P host`, and calls go through a stateless
      `CallRel` oracle. A run's host-event log cannot be recovered from it, and a stateless host
      cannot encode one, so the logs need a logged CFG layer. It reuses the CFG graph, extraction
      and control rules, and the canonical store-retaining logged relation
      `HostClosingS.EvalLXPS` (open calls with arbitrary answers: values, an exception raised at
      the call, or a callee trap with its store).
      - **H1, the logged machine `MStepL`.** A block-CFG execution: each block runs its straight-line
        segment by `EvalLXPS` on `liftInstrs sg.body` (flat ops by `evalFlat`, calls open and
        logged), then its terminator with `MStepC`'s rules (label frames, `goto`, `brVals`,
        `topVals`, loops, the function label, `try_table` frames and `Catches`, pending tail
        calls). It is never a native evaluation of the whole structured function in one step.
        Machine stacks are bottom first and native ones top first (`reverse`). Obligations:
        - a projection to `MStepC` on their shared fragment, with its hypotheses stated where
          host observations cannot be forgotten;
        - the forward theorem (the first bounded PR): a logged run from the CFG entry to an end
          (`exit`, `trap` with its store, an uncaught exception, a pending tail call) with log
          `l` is an `EvalLXPS` run of the body with exactly `l` and the store.
      - **H1 status (done here): the logged machine and the forward theorem**
        (`Wasm/Cfg/MachineL`).
        - `MStepL`: each block's straight-line code runs by `EvalLXPS`, then the native outcome
          is dispatched (`DispL`) to `MStepC`'s CFG targets, with **native stack conventions** at
          frame boundaries (coordinator-approved option B).
          - Leaving an arm keeps the top `nr` values over the frame's outer values (`popN`,
            `gotoN`).
          - A branch keeps the label's arity of the branch-site stack (`branchN`).
          - `return` and a branch out of the function exit with the branch-site stack.
          - Arities come from the block type (`Binaryen.arity`), with no run-time checks.
          - Entering an arm and re-entering a loop split the stack as `EvalLXPS` does
            (`stk.take np`, `vs.take np ++ outer`), so no step is missing on short stacks.
          - `MStepC` keeps Core's conventions. The two agree on typed code; no untyped
            correspondence is claimed.
        - `forward_sink`, `forward_tail`: for **all code**, a logged run from the CFG entry to a
          sink (or to a pending tail call) is an `EvalLXPS` run of the body. The log, final store
          and frame are exactly the run's, and the result is one the sink stands for (`EndRel`).
          This covers stores kept by traps, and tail calls bypassing handlers.
        - The proof is an invariant (`Good`, `KL`, `WrapL`) carried backwards along the run: at
          each block the rest of the sequence runs natively, and each enclosing structured
          instruction's native rule carries the outcome out.
        - Fixture `Wasm/Cfg/ExampleLogged`: on an invalid body the logged machine exits with `3`
          (native) and `MStepC` with `1, 2, 3` (Core).
        - Run-level projection, done (`Wasm/Cfg/MachineLProj`, `project_sink_closedX`). A logged
          run from the CFG entry to a sink is an `MStepC` run to a sink with the same native
          result (`EndRel`, `ResOut`, `EndsC`). It composes `forward_sink`, `closed_iff_logged`
          and `native_machine_closedX`. Its fragment is stated:
          - every logged entry is answered by `closedXOk`, the typed closed extended oracle;
            host entries never are, so a log with a host call does not project;
          - direct calls only (`xFreeL`), no exceptions (`ehFreeL`), `TypedT` for `tExt`.
          It does not count as the stepwise projection. These restrictions are not its final
          coverage.
        - Still open in H1, in order:
          1. The stepwise typed stuttering projection `MStepL` → `MStepC` on the shared no-EH
             fragment. It needs a typed state and frame invariant, from the existing checker and
             typing APIs, covering stack orientation, parameter and result arities, normal arm
             exits, branch unwinding and tail-frame replacement. The relation is at block
             granularity (zero or more `MStepC` steps per `MStepL` step), with composition.
          2. An `EvalOXP`/`EvalOXE` → Core bridge for exception outcomes (`ehExt`). It must keep
             the exception outcomes, tag matching, trap stores, and tail calls bypassing the
             caller's handlers. Then the stepwise projection extends to EH.
          3. Validated typed nested fixtures (block, loop, if, catch) on which it holds.
          The `CloseOk` hypothesis is discharged in the session/host result by the canonical
          store-retaining closing correspondence, not kept as an assumption that all logs are good.
        - Converse support: `MachineLSeq.split` (a run of `es₁ ++ es₂` falls through `es₁` then runs
          `es₂`, or ends abruptly in `es₁`), the converse of `append`.
        - Converse design (next PR): induction on the native derivation, level by level.
          - At sequence level `p`, a native run of the rest of the sequence from block `i` gives
            a machine run to the state that `DispL` (or the fall-through to `contRev`) assigns to
            its outcome.
          - Structured terminators recurse on the arm's derivation, then on the parent's
            continuation derivation (both sub-derivations).
          - `loopBack`'s re-run of `.loop :: rest` is a sub-derivation started from the arm
            entry, not from the segment. So the induction's start states are "the point where a
            structured instruction is entered", which covers both the fresh entry (`enter`) and
            the re-entry (`branchN`).
      - **H2 status: the converse for finished outcomes is done** (`MachineL.backward`).
        - Hypotheses: a native run of the body to `r`, where `r` is not `brk (k + 1) _`. So `r`
          is a fall-through, `return`, `brk 0`, a trap, an uncaught exception, or a pending tail
          call.
        - Conclusion: a logged run from the CFG entry to an end standing for `r` (a sink, or the
          block making the pending tail call), with exactly the native log.
        - The excluded class: a native body outcome `brk (k + 1)` (a branch past the function
          label) can exist on invalid code. It has no machine end (no `DispL` rule) and no framed
          finished counterpart (`exitFlow` gives `none`, so no `wasmHOpenXPS` behaviour).
        - Proof: continuation passing on the native derivation (`MachineLBwd`). The motive
          covers mid-segment positions and arm entries, so `loopBack`'s re-run of the loop
          starts where the machine re-enters it.
        - The re-entered loop frame's arity is now the block type's parameter count, the same as
          a fresh entry.
        - **Pending calls, done** (`MachineL.pending_iff`, both directions): the body reaches the
          internal call `z` after the native log `l` exactly when the logged machine runs from
          the CFG entry to a block reaching `z` (`ReachL`), the logs splitting `l`.
          - Encoding, coordinator-approved, as an internal witness only: answering the call with
            a callee trap (`reach_trap` for every trap store, `trap_reach` the converse,
            `trap_last`), then the finished correspondence.
          - The pending question, its pre-call store and the prefix log are the statement's; the
            synthetic trap store is not.
          - Pending tail calls are ends of the body (`TailL`), not pending internal calls.
          - Fixture `Wasm/Cfg/ExamplePending`: a call in a handler that is pending, answered by an
            exception (caught: exit) or by a callee trap (uncaught: trap); a tail call in a
            handler (`TailL`).
        - **Divergence, step D1 done**: `MachineL.closed_iff_logged`.
          - A closed run `EvalOXP C` is exactly a store-retaining logged run (`EvalLXPS`) whose
            entries are all `C`-answers (`CloseOk`).
          - Answers are exact: callee values trimmed to the callee's result arity; exceptions and
            traps with the stores `C` leaves.
        - **Divergence, D2 done** (`Silmaril.Wasm.Cfg.MachineLDiv`). The machine's host-free
          divergence has three distinct forms, every logged call answered by `closedCallXP`
          (`StepK`):
          - `InfK`: an infinite run of local steps;
          - `CalleeDivK`: a finite run to a reached call (`ReachL`) whose callee diverges at the
            frame (`FunDivXP`);
          - `TailDivK`: a finite run to a pending tail call (`TailL`) whose callee diverges. This
            one is function-level only.
          `MDivL := InfK ∨ CalleeDivK`; `FunDivL` adds `TailDivK` at the frame, as `funDivXP_iff`
          does.
          - `div_iff`: `EvalDivXP s f [] (liftInstrs body) ↔ MDivL body (initial body s f)`.
          - `funDiv_iff`: `FunDivXP s a args ↔ FunDivL s a args`.
          - Native to machine: the infinite run is built from the native unfolding. Finite parts
            of structured instructions go through the converse's arm clause, with a strict stop
            state, so every unfolding makes at least one machine step.
          - Machine to native for `InfK`: coinduction on `EvalDivXP` over positions of the run.
            Steps are classified by depth (`MStepS`): re-entering a loop counts as leaving its
            arm. At the first step leaving an arm, the arm's run is read natively by a forward
            invariant relative to the arm's frame (`Proofs/Wasm/Cfg/MachineLRel`, `arm_fwd`).
        - **Divergence after a log, D3 done.** `MLogDivL body st l`: logged steps, then a
          boundary inside a step, then host-free divergence (`MDivL`, or a reached call whose
          callee diverges). The log is the calls before the boundary.
          - Native to machine, exact log: `logDiv_machine`. `LogDivXP s f [] (liftInstrs body) L`
            gives `MLogDivL body (initial body s f) (L.map OCall.toS)`.
          - Machine to native, up to oracle-answered calls: `machine_logDiv`. `MLogDivL ... l`
            gives `LogDivXP ... L` with `L.map OCall.toS = l ++ c`, every entry of `c` a
            `closedCallXP`-answer. `LogDivXP` places the boundary only where the remaining
            subproblem diverges; the machine's may come earlier, the run then leaving that
            sequence through closed calls. The closure resolves such entries with empty host logs.
          - Proof of the converse:
            - the run after the boundary eventually never leaves a sequence (`stays_point`: a
              block, or the arm entry of a loop re-entered forever), so that point diverges
              natively (`MachineLDivI.qx_div`);
            - the logged run from the CFG entry to it is a `LogDivXP` prefix (`prefix_logDiv`, a
              finite-horizon version of the coinduction, with arms left read by `arm_fwd`);
            - a diverging callee goes through the pending-call correspondence (`reach_logDiv`).
        - **Productive streams, P1 and P2 done (both directions).** `ProdL body st ω`: an infinite
          logged machine run whose step logs concatenate to `ω`, with infinitely many calls.
          - `infL_machine`: `InfLXP s f [] (liftInstrs body) ω` gives
            `ProdL body (initial body s f) (fun n => (ω n).toS)`, the same stream. The proof is an
            induction on `InfLXP`, as for divergence after a log. A loop iterating forever is the
            chain of its iterations on the machine (`prod_of_chain`, each iteration a nonempty run
            from the arm's entry back to it).
          - `machine_infL` (P2, machine to native, exact stream): `ProdL body (initial body s f) ν`
            gives `InfLXP s f [] (liftInstrs body) ω` with `ν = fun n => (ω n).toS`. `prodL_iff`
            states both directions together.
          - Proof of P2 (`Proofs/Wasm/Cfg/MachineLProdB`): a strong induction on the size of the
            remaining code, at positions of the run that never leave their sequence (`claims`:
            the block claim `PBC` and the arm-entry claim `PAC`).
            - An arm the run never leaves is a descent.
            - An arm left forward is a finished instruction, read natively by `arm_fwd`
              (`first_leave`).
            - A loop re-entered finitely often ends in `loopBack` iterations.
            - A loop re-entered infinitely often is `loopInf`. Its stream is the iterations'
              concatenation, the same stream as the run's tail (`streamConcat_unique`).
        - The closed oracle `closedCallXP` used here is the native one. These results do not
          discharge H3, which still needs the recursive logged CFG closure.
        - Still open as fixtures: nested-loop `continue` and a tail call inside a handler.
      - **H2, both directions on bodies.**
        - Finished ends: done, throw and trap, with exact final store and log.
        - Pending calls (`ReachLXPS`), quiescent divergence, and coherent productive streams.
          These are proved for the machine, not inferred from finite equivalence.
        - EH: handler matching (`Catches`), and pending tail calls bypassing handlers.
        - Stack caveat: a native `return`/branch flow carries only the innermost stack, while
          the machine keeps the whole frame stack, so an exact equality of result values needs
          typing, as in `ExampleExitStack.machine_loss`. The typing hypotheses are stated, not
          hidden.
      - **H3, the recursive CFG closure.** `cfgHOpenXPS`, the open module whose Wasm bodies run
        on the logged machine. It is defined from the machine, not as an alias of `wasmHOpenXPS`.
        Its closure `Shape.close cfgHOpenXPS` resolves callees through CFG-run bodies, which
        discharges `CX closedCallX`.
        - Equality with the store-retaining session closure `wasmEvFunXPS`/`sessionTripleXP`
          (not the trap-store-erasing `wasmEvFunXP`).
        - Then the instance session with imports and exceptions, via the existing Core adequacy
          (`wasmEvFunXPS_*_iff`, `wasmEvPendXPS_eq`, productive streams) and NodeBridge, on a
          typed fragment with the exception checker (`ehExt tags`).
        - Regressions: recursion through a host, trap-then-resume, productive host interaction.

**Also tracked:** byte occurrence (a function's code entry in its module's bytes, for the valid
serializer profile) is not started. Typing completeness for validated bodies is done
(`bodyIfaces_complete`).

## CFG variants: traps and raises

The legacy graph (**L**, `Cfg.Edge`) is kept unchanged, with its APIs, examples and
kernel-checked tables. The variants below are related to it by theorems, not by relabelling.

- **TE: traps as an abrupt outcome, raises as control.** This is the proposed default.
  - **Done** (`Silmaril.Wasm.Cfg.Variant`): `EdgeTE` is the legacy edges without the `trap`
    sink. `mustTrap` marks a block ending in `unreachable`; that is a terminal, non-returning
    outcome, not a state effect.
  - `edge_iff_te`: a legacy edge is exactly a TE edge, or the `trap` edge of a must-trap block.
  - `succOf_trap_iff`: only `unreachable` has a `trap` edge, because labels and continuations
    never resolve to `trap`.
  - `succTE_of_mustTrap`: a must-trap block has no TE successors.
  - May-trap marks (`Effect.mayTrap`) stay distinct from `mustTrap`.
  - **Next:** handler-resolved raise edges. A `throw`, or a call that may raise, gets edges to
    the `catch` targets of enclosing `try_table`s, innermost first, with an escape edge unless
    a `catch_all` covers it. A caught throw resumes; it is never terminal. These edges are to be
    proved against Core's `HANDLER` rules in the operational bridge.
- **AE: traps and raises both as outcomes, with resolved handlers.** This is the default the
  user chose.
  - **Done** (`Silmaril.Wasm.Cfg.Variant`): `succAE`/`EdgeAE` drop the `trap`/`raise` sinks and
    the `try_table` catch edges. `mustTrap`/`mustRaise` mark the abrupt outcomes, and
    `raiseHandlers` lists the possible handlers (enclosing catches, innermost first, then the
    caller unless a `catch_all` intervenes).
  - `edge_iff_ae`: a legacy edge is an AE edge, a must-trap `trap` edge, a must-raise `raise`
    edge, or a catch edge.
  - Explorer data: `variants["all-effects"]` and `variants["all-effects-instr"]`, with
    `default: "all-effects"` (`tools/wasm-pages/SCHEMA.md`).
  - The handler outcomes follow #230: a raise is control resumed by its handler, a trap is
    abrupt. They are to be proved against Core's `HANDLER` rules in the operational bridge.
- **Maximal blocks** (`Cfg.canMerge`, `canMerge_succ`, `canMerge_pred`,
  `canMerge_not_entry`): AE blocks are merged along a fallthrough whose target has no other AE
  or handler predecessor and is not the entry. The explorer's default is
  `variants["all-effects-max"]`, which keeps each member's identity (`members`).
  `Cfg.Maximal`: merges are functional and injective (`canMerge_functional`, `canMerge_inj`),
  so the merged blocks are disjoint chains. The contracted graph's edges are exactly the AE
  edges other than the merged fall-throughs (`mem_maxFlow`), plus every handler edge
  (`mem_maxHandler`). This is a graph construction, not an execution theorem.
- **Graph analyses are per variant.** Removing a sink changes no dominator of the remaining
  nodes, since a sink lies on no path to another node; this is to be proved as a graph lemma.
  It does change postdominators and exit reachability, so those are stated per variant.
- **Renderer:** TE's new edge kinds get IDs in `tools/wasm-pages/SCHEMA.md` with a version bump,
  coordinated with the explorer's renderer, before any page switches its default.


## Paused: F6, the CFG ↔ `BodyM` correspondence (owner 0e76ca84)

F6 of the typed Wasm/CFG → `BodyM` functor plan is **paused**. It is not forgotten: it resumes after the critical component work, or when the coordinator reassigns it.

- **Done around it:** the CFG operational bridge, both directions, for typed trees at a deterministic profile with no host (`Cfg.Bridge.bridge_fwd`, `bridge_bwd*`, `Cfg.BridgeCfg.machine_native`; #786 #790 #791 #793 #795). The `BodyM` side is the canonical semantics `CallXP` with `ExposeP.denListXP`, `FunctorP.OpEquivP` and `BodyStrat.toDStratBody_denL_iff`.
- **Exact goal:** for a typed function body `es`, the block-CFG runs of its graph, labelled with call events, are the logged `EvalLXP` runs of `es`. As corollaries:
  - CFG-trace equivalence of two bodies coincides with `OpEquivP`;
  - the CFG view has the same canonical `DStrategy` (`toDStratBody (denL es)`).
- **Hypotheses expected:** typed trees; a deterministic profile for the bridge; the scope of #786–#795 (no host, and pending tail calls answered by every oracle).
