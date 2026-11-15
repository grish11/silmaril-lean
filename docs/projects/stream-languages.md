# Stream languages

A generic vocabulary for inputs that arrive incrementally (chunk by chunk, possibly
forever) and the languages that judge them. It does not depend on any concrete
execution model. Wasm components, WIT `stream<u8>` and byte representations are
connected through separate bridge modules, which instantiate these definitions.

It reuses Mathlib's `Language α` (`Set (List α)`) and CSLib's `ωSequence α`,
`ωLanguage α`, `ωSequence.flatten` and the topological safety/liveness notions
(`ωLanguage.IsSafety`, `ωLanguage.IsLiveness`).

## Topics

| Module | Contents |
| --- | --- |
| `Silmaril.Semantics.Streams.Defs` / `Thms` | Finite-or-infinite words (`Word α`), ∞-languages (`Lang α`), chunk streams (`Chunks α`), their limits and progress |
| `Silmaril.Semantics.Acceptors.Defs` / `Thms` | Incremental acceptors (`process`/`accepted`/`reset`) specified against a `Language α` over arbitrary client traces |
| `Silmaril.Semantics.StreamAcceptors.Defs` / `Thms` | Acceptor answers on unbounded chunk sessions, equal to the monitor verdicts |
| `Silmaril.Semantics.StreamMonitors.Defs` / `Thms` | Safety and liveness verdicts of chunk-boundary monitors, compared with the limit word |

### `Silmaril.Semantics.Streams` (namespace `Silmaril.Streams`)

Stable API:

- `Word α` with constructors `fin : List α → Word α` and `inf : ωSequence α → Word α`.
  `Word.ofList` and `Word.ofω` are its embeddings (`Function.Embedding`), and
  `Word.isCompl_range` says that their ranges are complementary.
  `Word.not_injective_ωSequence_list` (Cantor) shows there is no injection the other
  way. `Word.equivSeq : Word α ≃ Stream'.Seq α` (with `Word.toSeq`, `Word.ofSeq` and
  `Word.terminates_toSeq_iff`) connects it with Mathlib's possibly terminating sequences.
  `Word.HasPrefix`, `Word.prepend` and `Word.map` are also provided.
- `Lang α := Set (Word α)`, with `Lang.finPart : Lang α → Language α`,
  `Lang.ωPart : Lang α → ωLanguage α`, `Lang.mk`, and
  `Lang.equiv : Lang α ≃ Language α × ωLanguage α`.
- `Chunks α := ωSequence (List α)`. Chunks may be empty. The API:
  - `prefixAt cs n` is the input delivered by the first `n` chunks.
  - `Progressive cs` holds when infinitely many chunks are nonempty.
  - `Limit cs t` is the limit relation, `limit cs` its unique solution, and
    `Accepts L cs` means `limit cs ∈ L`.
  - `ofList` turns a terminating chunk list into a stream padded with empty chunks.
    `ofω` turns an infinite word into one-letter chunks.
- Main theorems:
  - `limit_spec`, `Limit.unique` and `limit_eq_iff`: every stream has exactly one limit.
  - `isInfinite_limit_iff`: the limit is infinite iff the stream is progressive.
    A stream that runs forever but stalls on empty chunks delivers only a finite word.
  - `limit_eq_of_cofinal` (rechunking): mutually cofinal prefixes give the same limit.
  - `limit_ofList`, `limit_ofω` and `limit_eq_flatten` (relates to CSLib's `flatten`
    when all chunks are nonempty).
  - `accepts_ofList`, `accepts_ofω` and `accepts_of_not_progressive`.

### `Silmaril.Semantics.StreamMonitors` (namespace `Silmaril.Streams`)

Stable API:

- `safetyω L : ωLanguage α` is the set of infinite words whose finite prefixes are all
  in `L`. It is a safety property: `isSafety_safetyω`, in CSLib's topological sense.
- CSLib's `L↗ω` is "infinitely many prefixes in `L`". `isLiveness_omegaLim` shows it is
  a liveness property when every word extends by a nonempty word into `L`.
- `Chunks.AlwaysAt`, `Chunks.InfOftenAt` and `Chunks.EventuallyAlwaysAt` are the
  safety, Büchi and co-Büchi verdicts of a monitor queried after every chunk.
- Main theorems:
  - With one letter per chunk the verdicts are exact: `alwaysAt_ofω_iff` and
    `infOftenAt_ofω_iff`.
  - With coarser chunks, safety of the limit implies the boundary verdict
    (`alwaysAt_of_mem_safetyω`) but not conversely (`alwaysAt_coarse_counterexample`).
    For liveness, the boundary verdict implies `L↗ω` (`mem_omegaLim_of_infOftenAt`).
  - On a finite limit `w`, the liveness verdicts only decide `w ∈ L`
    (`verdicts_of_limit_fin`, `eventuallyAlwaysAt_ofList_iff`). A stalled stream
    answers yes infinitely often without delivering an infinite word
    (`infOftenAt_stall`).

### `Silmaril.Semantics.Acceptors` (namespace `Silmaril`, `Silmaril.Acceptor`)

Stable API:

- `ChunkView χ α` says how a chunk reads as a list of symbols. Instances exist for
  `List α`, `Array α` and `ByteArray` (symbols `UInt8`).
- `Acceptor σ χ` has fields `init`, `process`, `query : σ → Bool × σ` and `reset`.
  A query may change the state, which models a finalising `accepted()`. `Pure` says it
  does not.
- Traces are `List (Event χ)` built from `process c`, `query` and `reset`. The API:
  - `run A s tr` gives the answers.
  - `specObs L tr` is the specified answers: membership of the input since the last
    reset.
  - `ResetSound` (reset is observationally equivalent to `init`).
- Correctness notions:
  - `CorrectInterleaved`: arbitrary interleavings.
  - `CorrectImmediate`: each `process` is followed by one `query`.
  - `CorrectFold`: process everything, then query once. `correctFold_iff_decides`
    restates it as `Silmaril.Accept.Decides`.
- Main theorems:
  - `correctInterleaved_iff_correctFold` and `correctInterleaved_iff_correctImmediate`,
    assuming `Pure` and `ResetSound`.
  - Purity is necessary: `answerOnce_not_correctInterleaved` and
    `finalizing_not_correctImmediate`.
  - `CorrectInterleaved.run_process_nil`: empty chunks change no answer.
    `specObs_eq_of_toSymbolTrace_eq`: rechunking changes no specified answer.
  - Symbol-at-a-time: `ofSymbols`, `toSymbols`, `correctInterleaved_ofSymbols` and
    `symbolCorrect_toSymbols`.
  - `reference` and `exists_correctInterleaved`: every decidable language has a correct
    acceptor, possibly with infinitely many states.

### `Silmaril.Semantics.StreamAcceptors` (namespace `Silmaril.Acceptor`)

Stable API:

- `boundaryAnswer A cs n` is the answer of `accepted()` after the first `n` chunks of
  `cs : ωSequence χ`.
- `boundaryTrace cs n` is the client trace of `n` process/query rounds.
- `view cs : Chunks α` is the stream of symbol chunks.
- Main theorems:
  - `boundaryAnswer_eq` (assumes `CorrectFold`), `run_boundaryTrace` (assumes `Pure`)
    and `run_boundaryTrace_eq` (assumes `Pure` and `CorrectInterleaved`).
  - `alwaysAt_iff`, `infOftenAt_iff` and `eventuallyAlwaysAt_iff`: an acceptor's
    verdicts are the monitor verdicts.
  - `mem_omegaLim_of_answers`, and `answers_of_limit_fin`, which is the
    no-progress caveat.

## Scope and limits

- These are statements about data and languages. They do not show that any program
  produces these streams; a bridge has to prove that for its execution model.
- Terminating inputs are `List (List α)`, and they are judged by `Language α` on their
  `List.flatten`. Unbounded inputs are `Chunks α`, and they are judged by `Lang α`
  on their limit. Progress (fairness of chunk delivery) is an explicit hypothesis
  wherever an infinite word is meant.
