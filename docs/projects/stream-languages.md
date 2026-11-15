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

## Scope and limits

- These are statements about data and languages. They do not show that any program
  produces these streams; a bridge has to prove that for its execution model.
- Terminating inputs are `List (List α)`, and they are judged by `Language α` on their
  `List.flatten`. Unbounded inputs are `Chunks α`, and they are judged by `Lang α`
  on their limit. Progress (fairness of chunk delivery) is an explicit hypothesis
  wherever an infinite word is meant.
