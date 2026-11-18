# wasm-acceptor-harness

Runs certificate-checking Wasm component acceptors under Wasmtime (pinned exactly, 50.0.0) and
writes a report of what was observed. Observations are tests, not proofs. The Lean claims about
the bytes are copied from the suite into the report so that the explorer can show them. The
harness does not check them.

```
cargo build --release --locked
target/release/wasm-acceptor-harness suites/*.json --out report.json   # what `make acceptor-report` runs
target/release/wasm-acceptor-harness suites/*.json --suite-filter farkas --case two-row
cargo test --release --locked
```

- `--suite-filter TEXT` runs only suites whose name contains `TEXT`. `--case NAME` runs only
  cases with that name. Both options can be repeated. If no case is selected, the run is an
  error.
- The exit status is non-zero when a case does not match its expectation.

## Adding a checker

Add a suite file `suites/<name>.json`. You do not need to change any code. The schema is
[`docs/schemas/wasm-acceptor-suite.v1.schema.json`](../../docs/schemas/wasm-acceptor-suite.v1.schema.json).

- **`artifacts`** maps an id to `{ path, sha256, source, claims }`.
  - `path` is relative to the suite file.
  - `sha256` is the pin. If the file does not match it, every case on that artifact is an
    `error`, and its claims are withheld.
  - `claims` lists what the Lean library states about exactly the pinned bytes. Each claim has:
    - `kind`, for example `component-level soundness (kernel-checked)` or `core-module soundness only`;
    - `level`: `component` or `core-module`;
    - optional `registry_name`, the name in `silmaril/artifacts.toml`;
    - `value`, the Lean value the bytes are regenerated from;
    - `scope`;
    - `theorems`: `[{ decl, module, states }]`.

    A claim requires `sha256`. Leave `claims` out when nothing is proved.
- **`cases`** is a list of `{ name, artifact, export, class, args, expect, expect_detail, note }`.
  - The export must return one `bool`.
  - `args` holds positional JSON values, one per parameter.
  - `expect` is one of `accepted`, `rejected`, `trap`, `error` or `unsupported`. Without it, the
    case is `unchecked`, which never counts as a pass.
  - `expect_detail` is a substring that the trap or error detail must contain. It requires `expect`.

Arguments are converted by the export's actual parameter types, which are read from the
component (`src/value.rs`):

| WIT type | JSON |
|---|---|
| `bool` | `true` / `false` |
| `s8` `u8` `s16` `u16` `s32` `u32` `s64` `u64` | an integer number in range |
| `f32`, `f64` | a number, or `"nan"`, `"inf"`, `"-inf"` |
| `char` | a one-character string |
| `string` | a string |
| `list<T>` | an array, or `{"$repeat": v, "count": n}` |
| `tuple<…>` | an array of that length |
| `record` | an object with exactly its fields |
| `variant` | `{"case": "name"}` or `{"case": "name", "value": v}` |
| `enum` | `"name"` |
| `option<T>` | `null` or `{"some": v}` |
| `result<T, E>` | `{"ok": v}` or `{"err": v}`, with `null` on a side that has no type |
| `flags` | an array of distinct flag names |

Any other type (resources, `map`, fixed-length lists, `future`, `stream`, `error-context`) is
not supported. So is an argument whose shape does not match its type. Both give the outcome
`unsupported` without calling the export.

## The report (`silmaril.wasm-acceptor-harness.report/v2`)

The report contains:

- `command`;
- `engine` (with its configuration);
- `suites` (name and description);
- `artifacts`: size, SHA-256, BLAKE3, the registry CIDv1, `pinned_sha256_ok`, `claims` (each
  with the `sha256` it was made for) and an optional `claims_withheld`;
- `cases`: typed signature, arguments, `expected`, an optional `expected_detail`, `observed`
  and `verdict`;
- `summary`.

The report has no timestamps, so a rerun on the same files writes the same bytes. CI checks
this against the committed `report.json`.

v2 added `suites`, `claims`, `claims_withheld` and `expected_detail`. The explorer still reads
v1 reports, which have no claims.
