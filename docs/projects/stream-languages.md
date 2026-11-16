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
| `Silmaril.Semantics.Tokens.Defs` / `Thms` | Streaming transducers from symbols to tokens, token chunk streams, and lexer-plus-token-acceptor composition |
| `Silmaril.Semantics.StreamMonitors.Defs` / `Thms` | Safety and liveness verdicts of chunk-boundary monitors, compared with the limit word |
| `Silmaril.Semantics.StreamBounds.Defs` / `Thms` | Whole-input, per-item and nesting-depth bounds; completeness relative to an explicit bound; per-chunk transport limits |

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

### `Silmaril.Semantics.Tokens` (namespaces `Silmaril.Streams.Transducer`, `Silmaril.Acceptor`)

This is the generic bridge from a symbol alphabet (bytes, characters) to a token or event
alphabet. Format-specific token types and grammars instantiate it elsewhere.

Stable API:

- `Transducer ρ α τ` has fields `init`, `step : ρ → α → ρ × List τ` (which commits
  tokens) and `flush : ρ → List τ` (pending tokens at end of input, not committed).
- `emitted w` is the committed tokens, which are monotone in `w`. `tokenize w` is
  `emitted w ++ flush (state w)`, the tokenization of the whole input. `pull T L` is the
  set of words whose tokenization is in `L`; it equals `Accept.pullSome` along
  `Accept.ofTotal tokenize` (`pull_eq_pullSome`).
- `tokenChunks T cs` is the tokens committed per input chunk. `Productive T cs` holds
  when infinitely many chunks commit a token.
- `Acceptor.lex T B` composes a transducer with a token acceptor. `query` flushes on a
  copy, so it is pure.
- Main theorems:
  - `emitted_mono`, `prefixAt_tokenChunks` and `tokenLimit_eq_of_cofinal`: rechunking
    the input does not change the tokens.
  - `tokenLimit_ofList`: a terminating stream delivers only the committed tokens.
    Flushed tokens need an explicit end of input.
  - `not_productive_silent`: input progress does not imply token progress.
  - `symbolCorrect_lex` and `correctInterleaved_lex`: if `B` is correct for `L`, then
    `lex T B` is correct for `pull T L` on every interleaving.
- `Tokens/Examples.lean` has `lines sep`, generic item framing for line-delimited
  streams. It does not interpret the items.
### `Silmaril.Semantics.StreamBounds` (namespaces `Silmaril.Streams`, `Silmaril.Acceptor`)

Stable API:

- `RunBound f n : Language α` is the set of words all of whose prefixes `p` have
  `f p ≤ n`. It is prefix-closed (`RunBound.of_isPrefix`), monotone (`runBound_mono`),
  decidable (`RunBound.decidableMem`), and exhausts all finite words (`iUnion_runBound`).
  Three instances are kept apart:
  - whole-input bound: `RunBound List.length n`, equal to
    `Accept.upTo List.length n Set.univ` (`runBound_length_eq_upTo`);
  - per-item bound: `ItemBound isSep n := RunBound (gap isSep) n`, where `gap` counts the
    symbols since the last separator;
  - depth bound: `DepthBound kind d := RunBound (depth kind) d`, where
    `kind : τ → BracketKind` classifies tokens as `opening`, `closing` or `neutral` and
    `depth` is the nesting depth with unmatched closes floored at `0`. `netDepth` and
    `Balanced` give the untruncated count; `depth_eq_netDepth` relates them.
- `Acceptor.SoundFold A L` and `Acceptor.CompleteFoldOn A L B` split `CorrectFold`
  (`correctFold_iff`). Completeness is antitone in `B` (`CompleteFoldOn.mono`), and
  completeness at every bound is full completeness on finite inputs
  (`completeFoldOn_univ_of_runBound`, `completeFoldOn_univ_of_iUnion`).
  `Acceptor.boundedReference L B` is sound for `L`, complete on `B`, `CorrectFold` for
  `L ⊓ B`, and not complete as soon as a word of `L` is outside `B`.
  `soundFold_iff_sound` and `completeFoldOn_iff_completeOn` restate `SoundFold` and
  `CompleteFoldOn` as `Silmaril.Accept.Sound` and `Silmaril.Accept.CompleteOn` (from
  `Accept.Bounded`) of the fold checker on chunk lists.
- Infinite words: `safetyω (RunBound f n)` is a safety property. No infinite word meets a
  whole-input bound (`safetyω_runBound_length`). Recurring separators meet an item bound
  (`mem_safetyω_itemBound_of_window`, `const_mem_safetyω_itemBound`,
  `repeatItem_mem_safetyω_itemBound`, `exists_mem_safetyω_itemBound_not_length`). A word
  that only opens leaves every depth bound (`not_mem_safetyω_depthBound`).
- `frameItems sep items` frames a finite item list, with each item terminated by `sep`.
  For separator-free items, `frameItems_mem_itemBound_iff` says the per-item bound is
  `Silmaril.Accept.itemsWithin List.length n`. `frameItems_mem_runBound_length_iff` says
  the whole-input bound is `Silmaril.Accept.totalWithin (length + 1) m`.
  `Silmaril.Accept.Items` owns item-level lists; this lemma connects them to symbol
  streams.
- `ChunkBound k cs` bounds every chunk by `k` symbols. For `k ≥ 1` every finite or infinite
  word is delivered by such a stream (`exists_chunkBound_limit`); for `k = 0` only the
  empty word is (`limit_of_chunkBound_zero`).

Assumptions, each a parameter rather than a fact:

- Soundness is unbounded. Completeness is relative to an explicit bound language `B`; a
  streaming acceptor need not have one.
- Per-chunk transport limits (for example WIT `list<u8>` lengths, 32-bit in the wasm32
  canonical ABI) are the parameter `k` of `ChunkBound`. They do not restrict the language.
- Acceptor state memory is not modelled. Which languages a bounded-state acceptor can be
  complete on is out of scope.
- Nothing here proves anything about concrete Wasm execution.

### `Silmaril.Formats.ByteStreams` (bridge to `Silmaril.Formats.Accept`)

- `ChunkView` instances for `KBytes` and `Formats.Bytes`, through `BytesLike.toBytes`.
  The `toList_eq_toBytes_*` lemmas show that every byte chunk view agrees with
  `toBytes`.
- `answer_iff_of_correctFold`: a `CorrectFold` acceptor answers yes iff the concatenated
  bytes of its chunks are in the byte language.
- `answer_single_iff`: fed one value as a single chunk, it answers yes iff `b ∈ᴮ L`.
- `exact_over`: as a Bool checker on single values it is `Lang.Exact` for `L.over β`.

## Scope and limits

- These are statements about data and languages. They do not show that any program
  produces these streams; a bridge has to prove that for its execution model.
- Terminating inputs are `List (List α)`, and they are judged by `Language α` on their
  `List.flatten`. Unbounded inputs are `Chunks α`, and they are judged by `Lang α`
  on their limit. Progress (fairness of chunk delivery) is an explicit hypothesis
  wherever an infinite word is meant.
