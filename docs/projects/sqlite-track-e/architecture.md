# SQLite Track E architecture

The [Lean inventory](../../../Silmaril/Machine/SQLite/Architecture/Defs.lean)
records the architecture figure's four enclosing groups, eleven components and
nine arrows. [Theorems](../../../Silmaril/Machine/SQLite/Architecture/Thms.lean)
check coverage, uniqueness, containment and edge consistency. Import
`Silmaril.Machine.SQLite.Architecture.All` for the diagram and the four group
interfaces. The [coverage inventory](coverage-v1.md) records what the
implemented contracts check and where they stop. The [replay guide](replay-v1.md)
records the landed pins and verification commands. The contract map below
captures the implementation plan at the diagram pin.

## Upstream pin

The [Architecture of SQLite](https://www.sqlite.org/arch.html) page fetched on
2026-11-26 says it was last updated 2025-05-31 13:08:22Z. Its architecture
figure is the inline `svg.pikchr` under Introduction. The banner image is
separate. The [immutable Fossil artifact for `pages/arch.in`](https://sqlite.org/docsrc/raw/702a00612bfe17b8728e1e4cff7dd19a15d605095d78fb1994fd92f3b0b32015)
contains the figure's Pikchr source and the architecture prose. The artifact
ID is the source's SHA3-256. The HTML digest also covers the site's generated
shell, which can change independently of the figure.

| Bytes | SHA-256 |
| --- | --- |
| Immutable `pages/arch.in` | `6b5084fd9c58a14b1284b66b8b239bf87057064985370fe8b269d4e34a0158a2` |
| Fetched `arch.html` | `e5e00e53255dc1093fc8c087ff31b84c93dc802366392bda14e3f085776f521a` |
| Figure from opening `<svg` through closing `</svg>`, inclusive | `dd371474f92db2d395398c48b78ca2a719c51badfa474386d563653813555216` |

To refetch the source and compare the live rendering, run in a scratch directory.

```sh
curl -fsSL https://sqlite.org/docsrc/raw/702a00612bfe17b8728e1e4cff7dd19a15d605095d78fb1994fd92f3b0b32015 -o arch.in
curl -fsSL https://www.sqlite.org/arch.html -o arch.html
python3 - <<'PY'
from pathlib import Path
import re

html = Path("arch.html").read_bytes()
svg, = re.findall(rb'<svg\b[^>]*class="pikchr"[^>]*>.*?</svg>', html, re.S)
Path("arch.svg").write_bytes(svg)
PY
sha256sum arch.in arch.html arch.svg
```

The figure is documentation with its own revision. The existing [Track A
source inventory](../sqlite-track-a/header-inventory/README.md) separately
pins SQLite release **3.54.1**, including the amalgamation digest and source
check-in `57520227c95396ce39ba6ecaac8d475b78dd3964`. The Track E graph
transcribes the architecture documentation. Any release-specific comparison
needs a separate source and build profile.

## Inventory and graph

The diagram contains four colored frames around white component boxes. It has
no standalone legend. The italic frame captions and fills identify the groups
below. `labelLines` retains the literal SVG text, including nonbreaking spaces
and the two-line captions for SQL Command Processor and Code Generator.
`label` gives the same captions on one line with normal spaces.

| Frame caption | Fill | Contained boxes | Group re-export |
| --- | --- | --- | --- |
| Core | `#d8ecd0` | Interface, SQL Command Processor, Virtual Machine | `Silmaril.Machine.SQLite.Core.All` |
| Backend | `#d0ece8` | B-Tree, Pager, OS Interface | `Silmaril.Machine.SQLite.Backend.All` |
| SQL Compiler | `#e8d8d0` | Tokenizer, Parser, Code Generator | `Silmaril.Machine.SQLite.Compiler.All` |
| Accessories | `#e0ecc8` | Utilities, Test Code | `Silmaril.Machine.SQLite.Accessories.All` |

`parent` maps each component to its frame. `containment` flattens that
hierarchy into directed group-to-member pairs. `diagramArrows` records the
drawn arrowheads exactly:

- Interface → SQL Command Processor → Virtual Machine → B-Tree → Pager → OS Interface
- SQL Command Processor → Tokenizer → Parser → Code Generator → SQL Command Processor

`calls` reads the arrows as component-level invocations, with two explicit
edits. The drawn Code Generator → SQL Command Processor arrow is the
bytecode handoff and is kept only in `diagramArrows`. Interface → Virtual
Machine is added for the step entry point described in the page's prose.
The drawn SQL Command Processor → Virtual Machine arrow stands for dispatch
at this abstraction level. These invocations do not resolve native call
sites or prescribe a Lean import graph.

`dependencies` records selected consumer-to-provider contracts. Interface
uses prepare, VM execution and utility services. The command processor
uses tokenization and code generation. The tokenizer supplies tokens to the
parser's push interface. The parser uses symbol-table utilities. Code
generation consumes the parser's statement representation and targets the
VM's program and observation contract. The VM uses B-Tree operations, the
B-Tree uses Pager, and Pager uses the OS interface. Test Code consumes
the Interface under test. The drawn Parser → Code Generator arrow points
forward along processing, while the Code Generator → Parser dependency
points to the provider of syntax. Accessories have no drawn arrows. Additional
test hooks, utility clients, SQL callbacks, and the host beyond the VFS
are outside these edge lists. Page Cache and Bytecode Engine in the prose
describe the Pager and Virtual Machine boxes respectively.

## Component contracts

Each proposed leaf below is relative to `Silmaril.Machine.SQLite` and can
expose `Defs` and `Thms` when it has a contract to publish. The architecture
headers depend only on Lean core. The future group modules re-export their
available leaf APIs and own no state; the aggregate change owns those
modules and the Accessories leaves.

| Diagram box / owner and target | Types, operations and states | Interpretation, correctness target and reuse | Unimplemented here |
| --- | --- | --- | --- |
| Interface · VM/frontend · `Interface` | Connection and prepared handle; prepare, bind, step, reset and finalize. Abstract catalog/session and result stream; concrete statement lifecycle with VM state, cache and backing. | Compose the command processor with the VM; project row/complete/error observations and session poststate to the applicable D executor. Reuse `Prepared.bindInt64`, `Executor`, `Bridge.execute_corresponds`. | End-to-end lifecycle composition, native C handles/ABI and full SQLite API. |
| SQL Command Processor · compiler/prepare · `CommandProcessor` | SQL text, resolved statement, prepare error, program; classify, resolve and prepare. Abstract checked catalog and point-read plan; concrete parse/resolve/code buffer. | Relate preparation to D's `CatalogExecutor.resolve` and `Executor.prepare`; distinguish scope rejection from ordinary errors. Compose tokenizer, parser and code generator for the admitted SQL fragment. | Complete prepare pipeline, schema invalidation, reprepare and general statement execution. |
| Virtual Machine · VM/frontend · `VirtualMachine` | Instructions, program and step outcome; execute to row, done or error. Abstract rows/stream and storage effects; concrete PC, registers, cursors and emitted rows. | Interpret instructions with Track A typed requests and relate completed observations to D, including declared failures. Reuse [`Formats.Sqlite.Vdbe`](../../../Silmaril/Formats/Sqlite/Vdbe/Thms.lean), `SqlValue`, `Bridge.transferCell` and C's finite stream observations. | Effectful VM integrated with the compiler and backend, additional opcodes, SQLite C VM and full Mem behavior. |
| Tokenizer · compiler/prepare · `Tokenizer` | Input bytes, tokens, spans and lex errors; scan and push. Abstract sequence of accepted lexemes; concrete byte cursor and token buffer. | Show ordered, bounded spans identify the input lexemes and that rejection is explicit. The existing [shell parser](../../../Silmaril/Formats/Sqlite/Shell/Defs.lean) offers fragment examples. | Separate checked scanner, full SQLite token rules and encodings. |
| Parser · compiler/prepare · `Parser` | Tokens, restricted AST and parse errors; consume tokens and finish. Abstract admitted grammar; concrete parser progress and partial AST. | Show accepted statements satisfy the fragment grammar and give the expected D `Statement` shape; preserve ordinary rejection. Reuse the existing shell query shape and D's statement and name types. | Checked token parser, complete grammar and Lemon correspondence. |
| Code Generator · compiler/prepare · `CodeGenerator` | Resolved plan, instruction/operand types and program; emit and validate. Abstract point-read query and observations; concrete instruction buffer, labels and operands. | Show emitted programs are admitted by the VM and preserve the projected D3 result and errors on the agreed profile. Reuse `Vdbe.Program`, shell `scan`/`seek` examples, D3 catalog lookup and C's result observations. | General SQL lowering, optimizer and a composed compiler-to-storage theorem. |
| B-Tree · storage · `BTree` | Page/row IDs, rows and cursors; seek, read, advance and admitted edits. Abstract ordered map/numbered pages; concrete packed pages and cursors over acquired bytes. | Reuse Track B's `leaf_represents`, `page_lookup_run_iff`, `finishAcquire_page` and typed bridge to connect bytes to lookup; retain errors and acquired state. Track A supplies a representative leaf edit. | General cursor and interior traversal, indexes, balancing and multi-page edits. |
| Pager · storage · `Pager` | Page requests, read/write outcomes and transaction phases; acquire/cache, mark or edit, commit/rollback. Abstract page store and journal order; concrete owned cache slots, backing handle state and trace. | Reuse `PageRead.Acquire.acquire`, Track A's `pagerHandler`, `pagerTwice_readOnly_cold_warm` and representative write `run_follows_schedule`. Validate actual poststates and completed VFS exchanges for each admitted profile. | Integrated pager and general transaction/locking protocol, WAL, durability and crash recovery. |
| OS Interface · storage · `VFS` | Typed requests/replies; open, read, write, size, truncate, sync and close where supported. Abstract handles and file bytes; concrete bounded `FileState` or supplied handler state and completed exchanges. | Reuse [`SqliteVfs.Thms`](../../../Silmaril/Machine/SqliteVfs/Thms.lean) for `readOnly_lawful`, `readWrite_lawful` and trace bounds. Relate a handler to the abstract range, mode and file laws, including short reads and errors. | New VFS integration, native OS/filesystem refinement, timing, randomness and lock implementations. |
| Utilities · aggregate · `Utilities` | Leaf-specific text, compare or conversion operations. Abstract comparison/conversion rules; pure concrete helpers over bytes or values, with symbol state kept by the caller. | Specify each helper at its call site and prove the applicable conversion or ordering law. Reuse `Text`, `Affinity`, and existing codec checks where their contracts apply. | Reusable utility leaf, native allocator/PRNG/printf parity and complete collations. |
| Test Code · aggregate · `TestCode` | Fixture input, expected observation and checker; run and compare. Abstract test oracle; concrete SQL, image/value and expected trace data. | Check the admitted profile's outcomes and guards against published contracts. Reuse `Silmaril.Machine.SQLite.Relational.Checks` and [shell fixtures](../../../tests/formats/sqlite-shell/check.py); keep fixtures under tests unless a reusable fixture API emerges. | Track E integrated fixtures and any claim about upstream test-suite coverage. |

Pin the shared VM program and observation types before code generation.
Storage can define typed effects while the compiler and VM are developed.
Compose concrete handlers in VFS, Pager, B-Tree order before binding the
VM to storage. Interface combines prepare and execution. Group re-exports
and tests follow the published leaves.

## Landed foundations

- Track A supplies typed interactions and observation/refinement, the staged
  read and the representative rollback-mode write. The typed read exposes
  the VFS path; the repeated adapter threads file, cache and exchanges.
  [Reading map](../track-a-reading-map.md) · [Implementation](https://github.com/hiloopai/silmaril-lean/commit/f4e150fb9424a0c030c6a662d18d078adbbbdd82) · [Typed read](https://github.com/hiloopai/silmaril-lean/commit/f20bc085ccf72ba77bfd882823a11deb60556a38) · [Repeated read](https://github.com/hiloopai/silmaril-lean/commit/26a59ab4f3131bde9cee45053d678fa5b961886f)
- Track B relates an admitted designated rowid leaf to a height-zero
  numbered-page B-tree. [Read bridge](../sqlite-track-b/read-bridge.md) · [Merge](https://github.com/hiloopai/silmaril-lean/commit/d9e5d55d09a67486e7b36eda29032f0ce1d6f9eb)
- Track C's `Silmaril.Semantics.Relational.All` supplies typed tables, query
  observations, refinement and UB. [Contract](../relational.md) · [Merge](https://github.com/hiloopai/silmaril-lean/commit/611702d27cc6e43cbb7f3ec74013246d39d322ef)
- Track D supplies SQLite values/affinity, checked catalogs, the point-read
  executor and the conditional Pager/VFS correspondence. Start at
  `Silmaril.Semantics.SQLite.Relational.All` or
  `Silmaril.Machine.SQLite.Relational.All`. The read bridge requires a bound
  location, and the repeated cold/warm equality has additional leaf and
  projection premises. [Handoff](../sqlite-track-d/handoff-v1.md) · [Merge](https://github.com/hiloopai/silmaril-lean/commit/c8b56fe407a733112f059d712f6cac6c0ba0891a)

## Checks

```sh
root=Silmaril.Machine.SQLite.Architecture
lake build --wfail +"$root".Defs +"$root".Thms
make check CHECK_TARGETS="+$root.Defs +$root.Thms"
for module in "$root.Defs" "$root.Thms"; do
  SILMARIL_REPLAY_MODULE="$module" lake env lean -DwarningAsError=true \
    tools/compiler-explorer/Replay.lean || exit 1
done
```

The finite proofs check the Lean transcription. The upstream source and
rendered SVG are the references for checking that transcription. Neither
the graph nor the planned contracts assert native C equivalence, full SQL
coverage, WAL, or crash recovery.
