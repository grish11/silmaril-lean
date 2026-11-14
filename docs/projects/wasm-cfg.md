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
4. **Exceptions as control** (#230): a `throw`, or a raise out of a call, resolves to the
   enclosing `try_table` catch target or leaves the function. The CFG gets resolved exception
   edges for this, proved against the `HANDLER` rules. This replaces `handler-unresolved` and
   the call → `raise` effect edge. Trap and raise stay distinct.
5. **Path theorem.** Every finite run prefix, and every infinite run, of a call-free body
   projects to an edge path from `cfgEntry`. Divergence is an infinite path.
6. **Precise effects.** Each `trap` edge is justified by a step that traps (no generic "may").
   The converse, that every such edge is reachable, is not claimed unless proved.
7. **Adequacy.** The reverse direction (CFG paths realised by runs, under data conditions),
   only if equivalence is claimed.
8. **Calls**, through an explicit call interface: a call node whose callee behaviour is a
   parameter (a `FRAME` run of the callee), first for direct calls.

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
- **Graph analyses are per variant.** Removing a sink changes no dominator of the remaining
  nodes, since a sink lies on no path to another node; this is to be proved as a graph lemma.
  It does change postdominators and exit reachability, so those are stated per variant.
- **Renderer:** TE's new edge kinds get IDs in `tools/wasm-pages/SCHEMA.md` with a version bump,
  coordinated with the explorer's renderer, before any page switches its default.

