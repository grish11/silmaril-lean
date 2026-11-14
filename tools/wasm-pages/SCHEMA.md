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
