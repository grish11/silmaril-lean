# Acceptor components: acceptance checklist

The status of each certificate-checking component acceptor, export by export: the artifact, its
interface, what is **proved** (kernel-checked Lean, every numerics profile `P` and every component
choice profile `prof` of the reference Component Model machine `core3P P` with the reference host),
and what is **tested** (Wasmtime 50.0.0 runs of the exact bytes; observations, not proofs). The
reusable layers are described in [acceptor-kit.md](acceptor-kit.md), the semantics in
[consequence.md](consequence.md#word-carriers-listlists32-and-zero-terminated-lists32) and the
observations in [accepted-inputs.md](accepted-inputs.md).

Reading of "accepts" and "rejects": the theorems are about the behaviours of the reference machine
that instantiates the component and calls the export. **Sound** means every behaviour returning
`true` has its input in the language. **Never accepts** means no behaviour returns `true`. Neither
states that a call terminates or that `false` is returned (termination is not proved), and no
completeness is claimed.

## Artifacts and their identity

| Component | File | CID | Registered value | Identity certificate |
|---|---|---|---|---|
| SAT | `examples/wasm-acceptors/sat_accept.wasm` (960 B) | `bafkr4icjfaoiep3z6hfvly3knk6l3pm67ibllbgadje6vjqyprqknpvgqa` | `silmaril.selftest.wasm_acceptors.sat_accept` | `sat_accept_is`, `sat_accept_bytes` (file = `SatAccept.bytes`), `sat_accept_toRef` |
| LRAT | `examples/wasm-acceptors/lrat_accept.wasm` (3198 B) | `bafkr4ihc3lsk4fcp2plsi7mwqub34h7edj6i6kssyqhezdahivctjiz7km` | `silmaril.selftest.wasm_acceptors.lrat_accept` | `lrat_accept_is`, `lrat_accept_bytes`, `lrat_accept_toRef` |
| Farkas | `examples/wasm-acceptors/farkas_accept.wasm` | `bafkr4igd5n4qywsi5wnzogjwvltd3chsrjoa6um4ed6cb5o5vig73jztka` | `silmaril.selftest.wasm_acceptors.farkas_accept` | `farkas_accept_is`, `farkas_accept_bytes`, `farkas_accept_toRef` |

The CID pins the file (`silmaril/artifacts.toml`, checked by `sil project lock`); the `.is`
certificate (`examples/project/ProjectSelfTest/WasmAcceptors.lean`, kernel evaluation of the
encoder against the included file) proves that the file is the Lean value `bytes`, which parses to
`c.toAst coreBytes`, whose reference reading is `c.toRef` (`Acceptor.toRef_toAst`, for every
`ListComp`). `sil project check` reports the six `.is`/`.parses` problems as THM
(`examples/project/check.txt`).

## Exports

### SAT, nested: `check-nested(problem: list<list<s32>>, model: list<s32>) -> bool`

| | |
|---|---|
| Language | `SatNested` (`decodeNested`: a `0` or `Int32.MIN` in a clause is malformed) |
| Lean checker | `satNested` (explicit consistent model witness, `satNested_sound`) |
| Core | `nested_returns`: every returning run answers `1` iff `satNested` of the words in memory |
| Component sound | `SatAccept.checkNested_sound` / `checkNested_satNested` / `checkNested_accepts` |
| Bytes / registered value | `checkNested_sound_of_bytes`, `sat_accept_checkNested_sound` |
| Never accepts | malformed problem (`checkNested_rejects_problem`), non-literal model word (`_rejects_nonLit`), inconsistent model (`_rejects_inconsistent`), an unhit clause (`_rejects_clause`), any input where `satNested` is false (`checkNested_rejects`) |
| Tested | `suites/sat.json`, `nested-*` cases (positive, empty formula `[]`, empty clause `[[]]`, inner `0`, `Int32.MIN`, too-large input) |

### SAT, stream: `check-stream(problem: list<s32>, model: list<s32>) -> bool`

| | |
|---|---|
| Language | `SatStream` (`decodeStream`: `Int32.MIN`, or a last clause without `0`, is malformed) |
| Lean checker | `satStream` |
| Core | `stream_returns` (answer `1` iff `satStream`) |
| Component sound | `SatAccept.checkStream_sound` / `checkStream_satStream` / `checkStream_accepts` |
| Bytes / registered value | `checkStream_sound_of_bytes`, `sat_accept_checkStream_sound` |
| Never accepts | malformed problem, non-literal, inconsistent model, unhit clause, `satStream = false` (`checkStream_rejects*`) |
| Tested | `suites/sat.json`, `stream-*` cases (empty stream, `[0]`, unterminated, `Int32.MIN`, extremes `±(2³¹−1)`) |

### LRAT, nested: `check-nested(problem: list<list<s32>>, cert: list<s32>) -> bool`

| | |
|---|---|
| Language | `UnsatNested` |
| Certificate | flat LRAT stream v1 (`LratStream.decode`: RUP, deletion, RAT steps) |
| Core | `LratAccept.checkNested_sound`: a nonzero answer gives `UnsatNested` and a decoding certificate |
| Component sound | `LratAccept.Component.checkNested_sound`, `checkNested_cert` |
| Bytes / registered value | `checkNested_sound_of_bytes`, `lrat_accept_checkNested_sound` |
| Never accepts | malformed problem (`checkNested_rejects_problem`), malformed certificate, i.e. `LratStream.decode cs = none` (`checkNested_rejects_cert`, from the driver's parse automaton `certRun`, `decode_of_certRun`) |
| Tested | `suites/lrat.json`, nested cases (RUP, RAT, deletion certificates; bogus and missing hints; malformed problems and certificates) |

### LRAT, stream: `check-stream(problem: list<s32>, cert: list<s32>) -> bool`

| | |
|---|---|
| Language | `UnsatStream` |
| Core | `LratAccept.checkStream_sound` |
| Component sound | `LratAccept.Component.checkStream_sound`, `checkStream_cert` |
| Bytes / registered value | `checkStream_sound_of_bytes`, `lrat_accept_checkStream_sound` |
| Never accepts | malformed problem (`checkStream_rejects_problem`), malformed certificate (`checkStream_rejects_cert`) |
| Tested | `suites/lrat.json`, stream cases |

### Farkas: `check(system: list<ineq>, y: list<s64>) -> bool`, `record ineq { coeffs: list<tuple<u32, s64>>, bound: s64 }`

| | |
|---|---|
| Language | `Infeasible` (no solution over any ordered field) |
| Lean checker | `farkasCheck` (`checkCert`, `farkasCheck_sound`) |
| Core | `FarkasAccept.check_sound`: a nonzero answer gives `Infeasible` and one multiplier per inequality |
| Component sound | `FarkasAccept.Component.check_sound`, `check_length` |
| Bytes / registered value | `check_sound_of_bytes`, `farkas_accept_check_sound` |
| Never accepts | a multiplier list of the wrong length (`check_rejects_length`) |
| Tested | `suites/farkas.json` (two- and three-row refutations, scaled, repeated variables; feasible, negative, wrong and missing multipliers; the module's bounds) |

## Semantically sound, not faithful to the Lean reference checkers

The components are sound for the languages; they are **not** proved to accept exactly what the Lean
reference acceptors `lratNested`/`lratStream`/`farkasCheck` accept.

* LRAT accepts a problem containing an empty clause (`[[]]`, the stream `[0]`) with the empty
  certificate: the streaming checker records the empty input clause as a refutation. The reference
  `LRAT.check` requires a step deriving the empty clause, so `lratNested [[]] [] = false`. The
  answer is sound (the problem is unsatisfiable); the case is marked in `suites/lrat.json`.
* The Wasm checkers are bounded and reject (as observed, not proved) well-formed inputs beyond their
  bounds that the Lean checkers accept: see below.

## Not proved

* termination, and that a rejected call returns `false` rather than trapping or diverging;
* rejection of well-formed inputs beyond the checkers' bounds: LRAT ids `≥ 1024`, literals with
  `|l| ≥ 1024`, a full clause arena; Farkas coefficients, bounds or multipliers beyond `2³⁰`,
  negative multipliers, variables `≥ 8192`, accumulator overflow; inputs beyond the 1 MiB ABI
  memory (the canonical ABI's bounds check fails; Wasmtime reports a host error) — tested only;
* that an LRAT certificate which decodes but does not refute the problem is rejected (only soundness
  constrains it; no agreement with `LRAT.check` is proved), and the analogous Farkas statement;
* any property of engines other than the reference machine: Wasmtime runs are observations.

## Checks to rerun

* Lean: `hiloop prove build` of the `Component.Thms`, `Project.WasmComponents.*Accept.Thms` and
  `ProjectSelfTest.WasmAcceptors` modules (CI builds the whole library with `--wfail`);
* `make project-check` (self-test; the six certificates are THM in `examples/project/check.txt`);
* `make acceptor-report` (Wasmtime; byte-reproducible report, diffed in CI);
* the Pages workflow's browser tests (`tests/explore/acceptor_runs.mjs` on the deployed site build).
