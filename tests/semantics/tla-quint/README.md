# Quint export fixtures for TLA+

Use the checked-in TLA+ files as concrete inputs and [oracle.json](oracle.json)
as the expected initial states and complete one-step relations on the listed
finite domains. Each state array follows the order in `variables`. Each
transition is a pair of state arrays in source, destination order. The exported
operators to check are `q_init` and `q_step`, which alias `init` and `step`.

| Fixture | Bounded states | Initial state | Raw `q_step` successors |
|---|---|---|---|
| [BoundedCounter](BoundedCounter.tla) | `0, 1, 2` | `0` | `0 → {1}`, `1 → {2}`, `2 → {}` |
| [BitPair](BitPair.tla) | `{0,1} × {0,1}` | `(0,1)` | `(0,0) → {(0,0),(0,1)}`, `(0,1) → {(1,0),(1,1)}`, `(1,0) → {(0,0),(0,1)}`, `(1,1) → {(1,0),(1,1)}` |

Both right-hand sides in BitPair read the source state. The false choice
swaps the bits, so in particular it sends `(0,1)` to `(1,0)`. The true
choice sends `(x,y)` to `(y,1-x)`. All listed states are reachable from the
respective initial state. The finite domains are test bounds on integer
valuations.

## Concrete syntax and dependencies

- Both files use a module header and footer, `EXTENDS`, singular `VARIABLE`
  declarations, block comments with Apalache `@type` annotations, and nullary
  definitions with `==`. The exporter lowers Quint initialization assignments
  to unprimed equality. Its step expressions use postfix prime, infix `:=`,
  conjunction `/\`, and the integer operators `<`, `+`, and `-`.
- BitPair uses a bounded existential `\E flip \in { FALSE, TRUE }:` for
  `oneOf`, with set enumeration, Boolean literals, and a parenthesized
  `IF … THEN … ELSE …` expression in the second update.
- Both files declare `EXTENDS Integers, Sequences, FiniteSets, TLC, Apalache, Variants`.
  Arithmetic and order resolve through `Integers`, which extends `Naturals`.
  `Apalache` defines `__x := __e == __x = __e`, so this operator constrains a
  successor value by equality. `Sequences`, `FiniteSets`, `TLC`, and `Variants`
  contribute no operators used by the fixture bodies. The bundled SANY in
  the pinned Apalache distribution resolves all six modules.
  [Apalache module](https://github.com/apalache-mc/apalache/blob/7954daf7563a69cce9d0b89c8542e40bf46f7c6e/src/tla/Apalache.tla)
- The exports stop at state and action predicates. The oracle includes the
  self-loops produced by BitPair at `(0,0)` and `(1,1)`. A later spec using
  `[][q_step]_vars` with the full state as `vars` adds a self-loop at each state
  by the bracket semantics, including the blocked counter state `2`. Neither
  export adds that bracket or a fairness clause. These checks cover the two
  finite graphs and leave temporal behavior, fairness, unbounded valuations,
  and general exporter correctness outside their scope. Quint itself
  postprocesses the pretty printer output for a known angle-action syntax
  issue, which these fixtures do not exercise.
  [Quint postprocessor](https://github.com/informalsystems/quint/blob/95141d4691cce7e60104bdfcbc1d1b074f1cb789/quint/src/tlaplusPostprocessing.ts)

## Provenance and opt-in checks

The Quint sources and oracle are original Silmaril fixtures under the
repository's MIT license. The `.tla` files are their byte-for-byte exporter
output, including whitespace and type comments. No upstream examples or
support modules are copied here. [Repository license](../../../LICENSE)

The exporter is Quint at commit
`95141d4691cce7e60104bdfcbc1d1b074f1cb789` (reports `0.34.0`), built from
its upstream lockfile. Quint sends flattened, analyzed JSON to Apalache's
TLA+ export RPC. The backend and the SANY/TLC distribution come from the
same Apalache `0.62.4` release (commit
`7954daf7563a69cce9d0b89c8542e40bf46f7c6e`). Both upstream projects are
Apache-2.0. [Quint exporter](https://github.com/informalsystems/quint/blob/95141d4691cce7e60104bdfcbc1d1b074f1cb789/quint/src/compileToTlaplus.ts)
· [Quint license](https://github.com/informalsystems/quint/blob/95141d4691cce7e60104bdfcbc1d1b074f1cb789/LICENSE)
· [Apalache release](https://github.com/apalache-mc/apalache/releases/tag/v0.62.4)
· [Apalache license](https://github.com/apalache-mc/apalache/blob/7954daf7563a69cce9d0b89c8542e40bf46f7c6e/LICENSE)

From the repository root, prepare the tools outside the checkout. Verified on
Linux x86-64 with Node `26.13.1`, npm `11.20.0`, and OpenJDK `21.0.13.1`.
The setup downloads sources, locked npm dependencies and the Apalache
archive. The checker uses local tooling and a loopback gRPC connection.
Reading the fixtures requires only the checked-in files.

```sh
tools_dir=$(mktemp -d)
git init -q "$tools_dir/quint"
git -C "$tools_dir/quint" fetch --depth=1 https://github.com/informalsystems/quint.git \
  95141d4691cce7e60104bdfcbc1d1b074f1cb789
git -C "$tools_dir/quint" checkout --detach FETCH_HEAD
npm --prefix "$tools_dir/quint/quint" ci

curl --fail --location --output "$tools_dir/apalache.tgz" \
  https://github.com/apalache-mc/apalache/releases/download/v0.62.4/apalache.tgz
tests/semantics/tla-quint/check.sh --check "$tools_dir/quint" "$tools_dir/apalache.tgz"
```

The checker requires archive SHA-256
`8ac8488422c30d552735bae11b92a2d014d8e02e8608702acc08f9a2d8a9abb2`.
It runs Quint's `compile --target=tlaplus` with explicit module, init, step
and backend flags. It compares the export bytes and verifies [SHA256SUMS](SHA256SUMS).
Use `--write` in place of `--check` to refresh the exports and hashes after
the semantic checks pass. The oracle is maintained as explicit expected values.

The semantic checker evaluates `init` in the pinned Quint TypeScript
interpreter, then injects each listed source valuation into the interpreter
and evaluates the original `step`. For BitPair it drives the single draw
through positions 0 and 1, checking that the evaluator requests exactly one
draw with bound 2 per evaluation. Each successful evaluation shifts the
complete next-state registers and checks the resulting valuation. The
counter's disabled step at `2` evaluates to false.

Separately, TLC invokes SANY on the generated files and exhausts the
reachable graph with `INIT q_init` and `NEXT q_step`. The checker compares
the initial labels, all reachable valuations and every edge in TLC's DOT
dump to the same oracle. TLC's `-deadlock` flag disables the deadlock
diagnostic so the counter's expected empty successor set is accepted.
