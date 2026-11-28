# IR registry

The explorer's **IR** page (`#/ir/`) lists intermediate representation
families, their typed program subsets and the semantics registered for each
subset. It links Lean declarations through the source view and institutions
through their existing logic graph pages.

## Writing records

Import `Silmaril.Project.Registry.IR.Defs` in a project registration module
reachable from the manifest's `modules`. Declare or import the referenced
records before using them. For example, the Arith registration uses:

```lean
silmaril ir_syntax_kind isolated_simple_regions := "Isolated single-block regions"
silmaril ir_family mlir.arith := "MLIR Arith dialect"
silmaril ir_subset mlir.arith.isolated := Silmaril.MLIR.Arith.Block
  (family := mlir.arith) (syntax_kind := isolated_simple_regions)
  (title := "Scalar arithmetic with scoped application")
silmaril ir_model mlir.arith.bitvector := Silmaril.MLIR.Arith.Block.denote
  (subset := mlir.arith.isolated) (semantics := denotational)
  (title := "Total bitvector denotation") (institution := ssa.mlir.isolated)
```

Each kind has its own stable name and SID in the project `objects` table.
Titles and documentation can change independently of these IDs. Several
models can refer to the same subset. Projects can add syntax kinds by
registering them. The model's reading must be `operational` or `denotational`.

Lean checks that the subset declaration is a type or an indexed family of
types and that the model declaration takes a program of that family. The
semantic reading comes from the author. An optional `institution` field
resolves to a Lean-checked institution registration. This reference is
catalog metadata. Mathematical comparisons are stated in the cited theorems.

## Landed registrations

| Subset | Syntax | Model and observation | Institution |
| --- | --- | --- | --- |
| `mlir.llvm.scalar` | Simple SSA, one block | `mlir.llvm.scalar_eval` evaluates admitted scalar blocks in order, yielding bits or immediate division-by-zero UB | |
| `mlir.arith.isolated` | Scalar SSA with isolated single-block application | `mlir.arith.bitvector` denotes a total function from typed environments to bitvectors | `ssa.mlir.isolated` |
| `mlir.cf.basic_scalar_loop` | Typed CFG at a fixed scalar loop profile | `mlir.cf.basic_scalar_loop_part` observes a partial singleton return | `ssa.mlir.cf.scalar_loop` |
| `mlir.cf.switch_assert` | Typed CFG with switch cases and assertions | `mlir.cf.switch_assert_run` executes with a finite block budget. `mlir.cf.switch_assert_part` denotes a return or abort, with divergence undefined. | |

The LLVM slice has regionless bodies. Scoped application belongs to the
landed Arith subset. The two pure MLIR institutions are bundled as
`ssa.mlir.regionless` and `ssa.mlir.isolated` for the logic graph. The Arith
link uses the existing `Silmaril.MLIR.Institution.Arith.translate_denote`
theorem at the arithmetic signature and bitvector model. The sequential LLVM evaluator
has no recorded institution link. [Arith correspondence theorem](../../Silmaril/SSA/MLIR/Institution/Arith/Thms.lean#L19) ·
[LLVM model](mlir-llvm-scalar.md) ·
[Pure institutions](mlir-institutions.md) ·
[Registrations](../../Silmaril/LogicGraph/Nodes/SSA/MLIR/Defs.lean)

Both CFG subsets belong to `mlir.cf` and use the `typed_ssa_cfg` syntax kind.
The Basic profile fixes the captured input widths, latch width, result width,
and interpreter. Its institution uses the registered observation to interpret
equations and termination sentences. `satisfaction_induced` preserves and
reflects satisfaction for admitted source sentences. For SwitchAssert,
`Cfg.mem_denotePart_iff` relates defined outcomes to finite runs.
[Basic profile and institution](sea-of-nodes-loop-mlir-institution.md) ·
[SwitchAssert semantics](mlir-cf-switch-assert.md#partial-denotation) ·
[CF registrations](../../Silmaril/LogicGraph/Nodes/SSA/MLIR/CF/Defs.lean)

## Export and checks

`silmaril.toml` imports the logic graph audit, whose node imports reach the
MLIR registrations. The ordinary `sil project dump` reads the Lean records and
declaration locations. `check` rejects duplicate keys and dangling references
to families, syntax kinds, subsets or institutions. `sqlite` writes
`ir_families`, `ir_syntax_kinds`, `ir_subsets` and `ir_models` to the same
database as `institutions` and `logic_nodes`. The explorer reads these tables
from its normal database.

```sh
make check CHECK_TARGETS=+Silmaril.LogicGraph.Nodes.SSA.MLIR.Defs
cargo test --locked --manifest-path tools/silmaril-project/Cargo.toml ir_registry
make project-check
```

To exercise the actual exported CF rows and the institution route in Chromium,
serve the `make project-check` output and run the focused browser check. Set
`PLAYWRIGHT_CORE` to the installed `playwright-core/index.mjs` if needed.

```sh
python3 -I tools/silmaril-project/tests/explore/pages_server.py \
  --root .lake/silmaril --port 8766 --log /tmp/silmaril-ir-requests.jsonl
# Run from another terminal.
node tools/silmaril-project/tests/explore/ir.mjs http://127.0.0.1:8766/explore.html
```

The IR page is a catalog. Syntax-specific program rendering, model comparison
views and registration of other developments are follow-up work.
