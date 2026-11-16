# wasm-pages data: stable identifiers

The explorer's Wasm pages and any other renderer read the files `wasm-pages` writes. These
identifiers are stable. A change to one is a breaking change: it is listed here and the
renderer is updated in the same pull request. Fields not listed here may be added freely.

## Files

| Path | Content |
| --- | --- |
| `wasm/index.json` | `{components: [Summary], modules: [Summary]}` |
| `wasm/functions.json` | `[[moduleSlug, funcIdx, displayName, export, blockCount]]` |
| `wasm/c/<slug>.json` | a component |
| `wasm/m/<slug>.json` | a module and its function bodies |
| `wasm/blob/<slug>.wasm`, `wasm/wat/<slug>.wat` | downloads |

`slug` is the item's `id` with every character outside `[A-Za-z0-9._-]` replaced by `~`. A
child's `id` is `<parent id>/module/<k>` or `<parent id>/component/<k>`.

## Function index

A module's `functions[i].idx` is the Wasm function index: imports first, then defined
functions. `bodies[j].idx` uses the same index space.

## Block CFG (`bodies[j].cfg`)

- **Nodes.** Block `n` is `cfg.blocks[n]`; renderers use the ID `b<n>`. Its identity is
  `(path, pos)`:
  - `path` is `"m/a.m/a…"`, the `SeqStep`s of `Silmaril.Wasm.Cfg.BlockId`;
  - `pos` is the block's position in the segmentation of that sequence.
  - `n` is the position in `Cfg.blocks`, the pre-order of `walk`.
  - Special nodes are the strings `"exit"`, `"trap"`, `"raise"` and `"invalid"`
    (`Silmaril.Wasm.Cfg.Target`).
- **Entry.** `cfg.entry` is a block number or a special node (`Cfg.cfgEntry`).
- **Edges.** `cfg.edges` holds `[from, to, kind]`, where `from` is a block number and `to` is
  a block number or a special node.

  | `kind` | Meaning | Lean |
  | --- | --- | --- |
  | `"flow"` | control edge of the structured-control relation | `Cfg.Edge` (`blockCfg_eq`, `edge_iff`) |
  | `"effect"` | syntactic "may" edge: a possible trap, or a raise from a call | `Cfg.EffectEdge` |

  Edge kinds may be added. Renderers ignore kinds they do not know.
- **Effect marks.** `blocks[n].effects` holds values from `"may-trap"`, `"call"` and
  `"handler-unresolved"` (`Cfg.Effect`).
- **Typing.** `blocks[n].typing` is `{in, out, inits, labels, branch}` from `Cfg.bodyIfaces`
  (`bodyIfaces_typed`, `bodyIfaces_lookup`, `bodyIfaces_complete`), or `null`.

## Graph variants (`cfg.model`, `cfg.bases`, `cfg.variants`, `cfg.default`)

These fields are additive, agreed with the renderer on #231. The top-level `cfg.edges` is
unchanged: it is the legacy **explicit-sink** graph (`cfg.model = "explicit-sink"`).

- **`cfg.bases`**: `[{id, kinds, relation, kernelTable?}]`, the dominator bases of a graph.
  - The legacy graph has `"flow"` (`Cfg.Edge`) and `"flow+effect"` (`Cfg.Edge ∪ Cfg.EffectEdge`).
  - `kernelTable` names the machine document whose dominator table the Lean kernel checked over
    that same basis. Only the five example functions have one.
- **`cfg.variants["all-effects"]`**: block level (`granularity: "block"`, same block numbering).
  - `edges` are `Cfg.succAE` as `"flow"` edges: the legacy edges without the `trap`/`raise`
    sinks and without `try_table` catch edges.
  - `"handler"` edges go from a raising block to its resolved handler block.
  - `relation: "Silmaril.Wasm.Cfg.edge_iff_ae"`: the proved translation to the legacy graph.
- **`cfg.variants["all-effects-instr"]`**: instruction level (`granularity: "instr"`).
  - `nodes` holds `[block, position]`; `position = instrs.length` is the block's terminator.
  - `entry` and edge endpoints index `nodes`.
  - Instructions in a block are chained by `"flow"`. A block's last node has `"flow"` edges to
    the first node of each AE successor.
  - This refines AE by splitting blocks; there is no separate theorem.
- **`outcomes`**: `[[node, effect, handler?]]`. These are what a node may do that is not an
  edge, and they are in no dominator basis.

  | `effect` | Meaning | Source |
  | --- | --- | --- |
  | `"trap"` | must trap: the node is `unreachable` | `Cfg.mustTrap` |
  | `"may-trap"` | may trap (division, memory, table, null, cast, array, or a call) | `Cfg.instrEffects` |
  | `"raise"` | must raise: `throw`/`throw_ref` | `Cfg.mustRaise` |
  | `"may-raise"` | a call may raise | `Cfg.Effect.call` |

  `handler` is given for `raise`/`may-raise`, one outcome per possible handler from
  `Cfg.raiseHandlers`: the catch targets of enclosing `try_table`s, innermost first. It is a
  node index, `"caller"` (escapes the function), or `"unresolved"`.
- **`cfg.bases`** of both AE variants: `"flow"` (`Cfg.EdgeAE`) and `"flow+handler"`.
- **`cfg.variants["all-effects-max"]`**: maximal basic blocks, with their own block numbering.
  - `blocks[k]` holds `path`/`pos` of its first member, `instrs` (the members' instructions,
    with inner terminators inline), the last member's `term`, the union of `effects`, and
    `members`, the shared-numbering blocks it contains, in order.
  - The variant-level `members` holds the same lists.
  - Edges are exactly `Cfg.maxFlow` and `Cfg.maxHandler` mapped to the groups:
    - every AE edge except the merged fall-throughs (`mem_maxFlow`, `internal_iff`);
    - every handler edge (`mem_maxHandler`).
    So a loop back into its own maximal block, including a one-block loop, stays a self-loop.
  - Outcomes are `[group, effect, handler or null, member]`. They are the member's AE outcomes,
    member by member and in order, so no effect's position is lost.
  - The groups are `Cfg.maxGroups`. They are published only if the checker `Cfg.groupsOk`
    accepts them. `groupsOk_sound` and `groupOk_spec` prove what acceptance means: every block
    is in exactly one group, and each group is a maximal merge chain. If the checker rejects
    the groups, no `all-effects-max` is published and the default is `all-effects`.
  - Typing stays per member: `blocks[k].typing` is `null`, and `memberTyping` holds each member's
    interface (or `null`). No interface is composed for the merged block, because entering a
    structured instruction between members changes the label context.
  - Chains are merged by `Cfg.canMerge`:
    - `canMerge_succ`: the earlier block's only AE successor is the next one;
    - `canMerge_pred`: no other AE or handler edge enters the next one, so label targets, loop
      heads and handler entries stay boundaries;
    - `canMerge_not_entry`;
    - `canMerge_functional`, `canMerge_inj` (`Cfg.Maximal`): merges form disjoint chains.
  - `relation` names these theorems.
- **`cfg.default`**: `"all-effects-max"`, the variant the page shows first. The legacy graph stays
  selectable as the explicit-sink consilience view.

Like the legacy graph, the AE graphs are syntactic: no theorem yet says that executions follow
them (the operational bridge in `docs/projects/wasm-cfg.md`).

## Call graph (`calls`)

`[caller, callee, kind, count]`:
- `caller` is a function index.
- `callee` is a function index, or for an unknown callee a string `"<kind>: <what>"`.
- `kind` is `"direct"`, `"tail"`, `"indirect"`, `"indirect-tail"`, `"ref"` or `"ref-tail"`.

## Provenance strings

The pages must keep each graph's caveats until a theorem removes them:
- **Block CFG:** syntactic and incomplete; no theorem says that executions follow it.
- **Call graph:** syntactic; not proved to cover the calls of a run.

The semantic proofs that will remove these caveats are tracked in `docs/projects/wasm-cfg.md`.
