# Wasm components: wasm-tools components, jco, WAC, WIT and the generator API

The second part of the Wasm tooling. It adds the WebAssembly component model to the Lean
`wasm-tools`, Lean versions of jco (`wasm-jco`) and WAC (`wasm-wac`), a WIT tool, the
command-line specification API, and the program generator API. The core `wasm-tools` and the
Binaryen tooling are described in [wasm-binaryen-tooling.md](wasm-binaryen-tooling.md) and
[wasm-tools-trust.md](wasm-tools-trust.md).

## Checked Declaration Wiring

`Silmaril.Wasm.Component.IntrinsicWiring` is an indexed builder for a flat
fragment of the reference component AST. Each step advances the actual
`DefState`. Core payloads supply the named module interface; instantiation,
aliasing, function type, canonical ABI, and re-export commands use the existing
reference checker. `Program.then` composes only fragments whose intermediate
scope agrees. `erase_nil` and `erase_then` give identity and composition in
the reference syntax; `erase_map` and `map_then` let a payload transformation
commute with erasure and composition when it preserves the accepted named
Core interface. `Program.sound` proves the actual `ValidComponent` judgment.

The regression links a typed provider exporting `get` to a typed consumer
importing `env.get`, then canonically lifts and exposes the consumer's `run`.
The erased program passes the reference Core 3.0 component checker. A missing
argument name and an out-of-scope provider instance are rejected. This is
scope-indexed **declaration** composition, not WAC composition of separately
closed components. Reference validation, not a new engine, supplies the
typing premises. The builder does not cover nested binders or resource declarations.

### Exact lift and typed exports

`IntrinsicWiring.Lift` seals a finished program as `Closed` at the reference
`ComponentType`. `Exposure` identifies an entry in that checked export table
by position, name, and actual entity type. `Closed.lift?` reconstructs the
indexed steps from reference syntax; its success certificate erases to the
input exactly. `Program.lift_erase` and `Closed.lift_erase` give the other
direction. This is a retraction on the supported declaration fragment, not
completeness for the full reference checker. In particular neither nested
components nor export ascriptions are silently stripped. `Closed.erase_map`
commutes with raw `Syntax.Component.map` for a payload map preserving the
same named module interfaces under one component profile.

### Observation boundary

`Closed.terminal_iff` relates the stock reference-machine outcomes at an
exposed function to `IRObs` of the existing component game. It requires
exact erasure to a `Simple.toRef`, `Simple.Adequate` (goodness, float freedom,
instantiation with the intended instance, flat arities), typed arguments and
a terminating outcome. It uses the stock no-import reference host. The
regression projects the same typed `add` declaration from an intrinsically
typed Core body and from a native Lime1 payload. For the Core projection of
the Lime1 payload, an actual game answer `x + y` transfers to the reference
machine. This is not an execution theorem about the native Lime1 engine.

`Syntax.Component Lime1.Module` and `checkLime1?` already exist: this is
shared reference component syntax with native Lime1 payloads and the Lime1
extern interface, not a separate Lime component calculus. That checker
checks wiring and the structural module interface, not Lime1 module bodies.
`Syntax.Component.map Lime1.Module.toCore` instead targets Core payloads:
the example rechecks at the Core 3.0 profile, whose extern types and module
validation are different. It does not coerce a native checked interface into
the Core index. Removing the adder's result-producing body leaves the native
interface check successful but is rejected by the Core-projected checker.

The [institution guide](wasm-institutions-guide.md#scope-core-modules-and-components)
describes the existing `componentToGInst` on component IR. A syntax map alone
does not give the reduct for native reference observations or the
satisfaction condition. The ready-instance Core `Entry` API begins after
registration. For actual linked components, `Linked2.sessObs_eq` needs the
adequate wire and the corresponding importer/exporter instances, discharged
within `Linked2.sessAdequacy_full` for that class;
`HLinked2.sessAdequacy_full` also requires typed host handling and retains
the host run. The flat Core-module wiring fixture proves neither the linked
instantiation/store correspondence nor an observation map for all prefixes.
The stock `Simple.adequacy` identifies only trap-last plays; observing the
retained store after a trap would distinguish its existing witnesses.

```sh
make check CHECK_TARGETS='+Silmaril.Wasm.Component.IntrinsicWiring.Lift.Observation.Thms'
```

## What ships

| Part | Modules | What it is |
| --- | --- | --- |
| Component model | `Silmaril.Wasm.Component` | the component binary codec behind one facade (`Codec`: `mvp`, `strict`, `async` and `lax` variants, with `mvp ⊆ lax` and `strict ⊆ lax` proved), the validator (proved sound), the canonical ABI, a reference component machine, resources, streams and futures |
| WIT | `Silmaril.Wasm.Wit` | WIT text and binary packages: parser, printer, elaboration and the custom-section encoding |
| jco | `Silmaril.Wasm.Jco`, `Silmaril.Wasm.JcoTool` | the transpilation of components to core modules and JavaScript glue, with the stream stack |
| WAC | `Silmaril.Wasm.Wac` | the WAC composition language: text, resolution and composition of components |
| Perf | `Silmaril.Wasm.Perf` | fast paths (validator, decoder, encoder, printer) used through `@[csimp]`; each states its equation with the verified version in `Thms` |
| Versions | `Silmaril.Wasm.Versions` | Wasm 1.0, 2.0 and Lime1 models with translations to Core 3.0 |
| CLI spec | `Silmaril.Cli.Spec.WasmTools`, `.Jco`, `.Wac`, `Silmaril.Cli.Clap` | the command lines as values, with derived help and usage errors |
| Generators | `Silmaril.Wasm.Tools.Gen` | `Gen.API` (core-only interface), per-model kits, the generators, mutators and shrinkers of `smith`, `mutate`, `shrink` and `wit-smith` |
| SpecTec | `Silmaril.Wasm.SpecTec` | the SpecTec headers that need the modules above: institution chains between 2.0 and 3.0, the remaining Sim10/Sim20 halves, `BinaryAgree`, the Lime1 grammar and simulations |

## Tools

| Executable | Source | What it does |
| --- | --- | --- |
| `wasm-tools` | `tools/wasm-tools` | the full build: the core subcommands plus `component new/wit/embed/targets/unbundle/semver-check`, `compose`, `smith`, `mutate`, `shrink`, `wit-smith`; every command line is read through `Silmaril.Cli.Spec.WasmTools.tool` |
| `wasm-tools-gen` | `tools/wasm-tools` | the generator subcommands alone |
| `wasm-tools-gen-check` | `tools/wasm-tools-gen-check` | measures how often each checked generator or mutator falls back |
| `wasm-jco` | `tools/wasm-jco` | a jco 1.39.0 work-alike (`transpile`, `new`, `wit`, `embed`, …) |
| `wasm-wac` | `tools/wasm-wac` | a WAC 0.12.0 work-alike (`compose`, `plug`, `parse`, `resolve`) |
| `wasm-wit` | `tools/wasm-wit` | WIT text and package tools |
| `wasm-perf` | `tools/wasm-perf` | runs the fast paths on inputs, for benchmarks |
| `cli-spec`, `cli-harness`, `cli-demo` | `tools/cli-*` | print and test the CLI specifications; a small demo program |

Build them with Lake:

```sh
lake build wasm-tools wasm-tools-gen wasm-tools-gen-check wasm-jco wasm-wac wasm-wit wasm-perf cli-spec cli-harness cli-demo
.lake/build/bin/wasm-tools component wit some-component.wasm
.lake/build/bin/wasm-jco transpile some-component.wasm -o out
```

## The `wasm-tools` command line, specified

The command line of `wasm-tools` 1.262.0 is a value: an argument grammar in the clap dialect
(`Silmaril.Cli.Spec.WasmTools.tool`) with every subcommand, option, positional argument, value
check and `requires`/`conflicts_with` rule of upstream. The executable reads every command line
with it before anything else.

- **Reading.** The clap pre-pass, then the argument parser proved sound and complete for the
  grammar, then the value checks and rules. When the pre-pass passes, the clap reading is proved
  to agree with the generic front end (`read_agrees`). The program reads as the spec
  (`WasmTools.toolAt_read`).
- **Help and errors are derived.** The `-h` and `--help` texts of every command path and every
  usage error are rendered from the grammar in clap 4.6's layout, byte-identical to upstream's
  on all 29 command paths at 100 and 80 columns and on 1096 of 1098 tested command lines (the 2
  others differ in the order in which upstream checks values).
- **Layout facts, proved.** Wrapping only inserts line breaks and indentation and drops trailing
  white space (`wrap_erase`); help and the version go to stdout and every usage error to stderr
  (`Tool.text_channel`); an error text starts with `error: `.

Where the layout puts its line breaks, and clap's wording, are tested against the pinned
binary, not proved.

## Program generators, mutators and shrinkers

`smith`, `mutate`, `shrink`, `wit-smith` and `wasm-tools-gen-check` are instances of one small
interface, `Silmaril.Wasm.Tools.Gen.API`, which needs only Lean's core library.

| Object | Meaning |
|---|---|
| `Rng`, `Rand` | SplitMix64, a splittable 64-bit generator, and seeded computations over it |
| `Lang`, `DecLang` | syntax with a validity predicate; a language with a Boolean checker proved equivalent to validity |
| `Generator L` | from a seed and a size, a program; every output is valid |
| `Mutator L` | a seeded rewrite that preserves validity |
| `SemMutator L Eqv` | a mutator whose output is `Eqv`-equivalent to its valid input |
| `Shrinker S` | a size and a candidate list; `Shrinker.shrink p x` greedily takes the first strictly smaller candidate satisfying `p`, and terminates |
| `ByteGen L`, `PMutator L` | the byte-seeded shapes of `wasm-tools smith` and `wasm-tools mutate` |

`Generator.guarded`, `Mutator.guarded` and `SemMutator.guarded` turn an unverified generator or
rewrite into a verified one: an output is kept when the checker accepts it, and replaced by a
valid default otherwise. The laws (`Gen.API.Thms`): checked shrinking keeps the predicate and
validity, never grows the input and ends in a local minimum.

`Silmaril.Wasm.Tools.Gen.Model` has a kit (checker, generator, mutator, shrinker) per model:
`kit10`, `kit20`, `kit30`, `kitLime1`, `kitFX`, and `coreKitT`/`kitFXT` whose generators are
valid by construction. `Gen.Comp` generates components and `Gen.Wit` WIT packages.

Trust boundary: the raw generators and mutators are unverified; validity comes from the checker
(a fast Core validator proved equal to the verified one) or from typing by construction. The
component validator is proved sound, not complete, so a checked component generator may fall
back where upstream would accept.

## Known limitations

- **Frozen statements.** Some results are stated as `def Task.x : Prop` and used only as
  hypotheses. Nothing unconditional depends on them. For the components and WIT:
  `Task.check_complete` (`Proofs/Wasm/Wit/Tool/Complete`), `Task.refToSpecFXE`,
  `Task.coreFraming_of_decode`; for the asyncify link to Core 3.0 (`FX/Asyncify/Tool`):
  `Task.machine_core`, `Task.fits`. For the CLI:
  `WasmTools.SpecThms.Task.*_agree` and `Wast.Spec.Task.*_agree` (the older core readers agree
  with the specification; tested on records with 0 differences). The SpecTec modules add
  `Task.composite*`, `Task.swapStep*`, `Task.unstripStep*` and a few others, described in
  [the SpecTec guide](spectec/README.md).
- **Raw modules.** About 200 modules under `Silmaril/Raw/Wasm/{Component,Versions,…}` hold
  valid but unrefined proofs, about 1,350 theorems of the component model among them. Headers
  re-export the parts other topics use.
- **Partial definitions.** `Tools/Component/Layout`, `Tools/Component/Typed`, `Wac/Text/Json`,
  `Wit/Binary/Print` and `wasm-tools-gen-check` still contain `partial def`s.
- **Upstream parity is tested, not proved.** The suites under `tools/wasm-tools/tests/
  {component,compval,gen}`, `tools/wasm-jco/tests`, `tools/cli-spec/tests` and
  `tools/cli-harness/tests` compare against pinned upstream binaries (wasm-tools 1.262.0,
  jco 1.39.0, wac 0.12.0, wasmtime 50.0.0) and skip when those are not installed; CI does not
  run them. Some read component fixtures that are not part of this repository yet. Last full
  run before release: jco suite 442 passed and 0 failed; the component validator agreed with
  upstream on 1896 of 1919 corpus components (13 valid ones rejected, 10 invalid ones
  accepted); `component new` agreed on 78 cases, both refused 15 and 22 differed; the CLI texts
  1096/1098.
- **Not implemented:** `wit-dylib` and `component link` report `not implemented in this build`.
