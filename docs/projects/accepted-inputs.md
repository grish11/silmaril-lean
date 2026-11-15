# Accepted inputs: byte languages, modules and components

What does a WebAssembly module or component *accept*? This development defines the set of
inputs a program accepts, as a language. It reuses the repository's Wasm and WIT semantics
and equivalences, and keeps every assumption explicit. Languages are sets, as in the generic
vocabulary of [`Silmaril.Semantics.Accept`](../accept.md); the set-level soundness and
completeness here agree with its Bool-checker forms (`Lang.sound_ofBool_iff`,
`Lang.complete_ofBool_iff`, `Lang.exact_ofBool_iff`).

## Modules

| Module | Contents |
| --- | --- |
| `Silmaril.Formats.Accept.{Defs,Thms,Examples}` | Acceptor sets `Lang α := Set α`; `Sound` (`A ⊆ S`), `Complete` (`S ⊆ A`), `Exact`; transport along encodings and decodings. `ByteLang := Language UInt8` (Mathlib). `BytesLike` covers `List UInt8`, `Array UInt8`, `ByteArray`, `KBytes` (with `KBytes.ofList` for the lawful instance) and `Formats.Bytes`; membership is `b ∈ᴮ L` (`ByteLang.Accepts`). Soundness and completeness are closed under `+`, `*` and `∗`. Byte languages are CSLib `Acceptor`s. Examples use a Mathlib `DFA` over bytes. |
| `Silmaril.Games.Accept.{Defs,Thms}` | Acceptance over any trace model or strategy (`observed`, `Strategy.accepted`). It is monotone in refinement. Observable-trace equivalence (`ObsEquiv`) preserves it, and so do move maps that commute with the observation. A generated strategy accepts exactly what its generating plays observe (`accepted_generate`). |
| `Silmaril.Wasm.Component.Reference.WIT.Interp.{Defs,Thms,Examples}` | Simple WIT types: the existing `WIT.ValType` with no `future` or `stream` (`ValType.simple`, `SimpleType`). `ValType.Interp E t` interprets them as Lean types (`u32 ↦ UInt32`, `s64 ↦ Int64`, `list ↦ List`, records ↦ products, variants ↦ sums, `flags ↦ BitVec n`, …); handles and names come from an environment `Env`. `ValLang E t` is the acceptor set at a type; `list<u8>` acceptors are definitionally byte languages; UTF-8 transports string acceptors faithfully. The canonical-ABI core signatures of the `accept` functions (`flattenFunc_accept_*`) and `layout_u8` are here too. |
| `Silmaril.Wasm.Game.Accept.{Defs,Thms,Examples}` | Core modules: `Callouts P Envs memIdx m` is the set of reachable import calls. A call records the import's name, its arguments and the bytes of memory `memIdx` at the call. Calls are collected after the specification's instantiation (`IsSpecInstance`), in sessions of the untyped game semantics (`UStep`) against every environment of the class `Envs`, which may also invoke exports with typed arguments. Accepted values come from decoders: `bytesLang` (`accept(ptr: i32, len: i32)`), `bytes64Lang` (memory64), `i32Lang` and `i64Lang`. `CalloutEquiv` is exactly the equivalence under which every decoder accepts the same values (`calloutEquiv_iff`). |
| `Silmaril.Wasm.Game.IOAccept.{Defs,Thms,Examples}` | Traced sessions of core modules (`TSession`): `Session`'s runs recording role tags (`Silmaril.Accept.IO.Tag`) decoded by `Roles` (export entry, result, `callIn`/`callOut` at a callout, `answerIn` on the host's answer). `ioRuns`/`entryIORuns` are the input-window and entry runs of `bracket '' tagTraces`, so `triggers`, `episodes`, `retTriggers` and `returns` apply to modules. See [I/O relations of modules](#io-relations-of-modules). |
| `Silmaril.Wasi.Component.Accept.{Defs,Thms,Examples}` | Components as WASI world models (`Strategy (nsig I) (nsig X)`, named events `WEv`). `bytesLang σ f` covers an imported `accept: func(list<u8>)`; `exportBytesLang σ f` covers an exported `accept: func(list<u8>) -> bool` that may return `true`. `valLang` and `exportValLang` do the same at any closed WIT type, through a strict decoder (`decode`) that follows the WASI value encodings. Acceptance is invariant under equality of named traces, monotone in refinement, and `CompEquiv` / `CompRefines` IR components (under any `Layout`) have equal / included acceptor sets. Every byte language is exactly accepted by a specification component (`importAcceptor`, `exportAcceptor`). |
| `Silmaril.Wasi.Component.Accept.Canon.{Defs,Thms}` | `CanonLowerAccept`: the correspondence a canonical-ABI adapter must establish between a module's `accept(ptr, len)` callouts and a component's `accept(list<u8>)` calls. Given it, the two byte languages are equal. |
| `Silmaril.Wasm.Examples.JsonAccept.Automaton.Thms` | The verified module's automaton as a Mathlib `DFA` over bytes (`intDFA`), presenting the subset (`DFAPresents intDFA intText`, #274). The embedded module accepts `{w ∈ intDFA.accepts \| w.length < 2^32}`. |
| `Silmaril.Wasm.Examples.JsonAccept.Exact.Thms` | Total correctness of `accept` (`TFSpecAt`; loop variant `len - i`, via `t_while` and the generator's total soundness for the loop-free body and tail). Existence of a returning run (`accept_exists`). Exact acceptance of the embedded module for every profile and host set containing a host: `exportAccepted = {w ∈ intText \| w.length < 2^32}` and `exportRejected = {w ∉ intText \| w.length < 2^32}`. |
| `Silmaril.Wasm.Game.Accept.Export.Defs` | Export reading for modules (`exportAccepted`/`exportRejected`): spec instantiation (`IsSpecInstance`), the instantiation run returns, the host writes the input into memory `0`, and some run of the named export on `[i32 ptr, i32 len]` (in bounds, `ptr + len < 2^32`) returns `[i32 1]` (`[i32 0]`). Hosts are a parameter. |
| `Silmaril.Wasm.Examples.JsonAccept.Instance.{Defs,Thms}` | The JSON-subset acceptor end to end. Its unique spec instance is computed by kernel evaluation, so the embedding is not vacuous. `exportAccepted ⊆ intText ⊆ JSON` and `exportRejected ∩ intText = ∅`, for every profile and host set. Termination and exactness are in `Exact.Thms`. |
| `Silmaril.Formats.Accept.Format.{Defs,Thms}` | The byte language of a `Silmaril.Formats.Format` (span `Bytes ← Derivation → Ast`): its valid inputs, the bytes some derivation produces. For a decoder it is the inputs it decodes (`lang_ofDecoder`); `ofLanguage` makes a format of a byte language. Format morphisms include languages. |
| `Silmaril.Wasm.Examples.JsonAccept.{Defs,Thms}` | **A concrete Wasm acceptor for a JSON subset**, verified against Core 3.0 execution at every profile and host. `accept(ptr, len)` scans memory with `i32.load8_u` and runs a branch-free 6-state automaton. A returning run answers `1` iff the segment is an integer text (`ws* -? (0\|[1-9][0-9]*) ws*`), so it is sound for JSON and exact for that subset; it is **not** a full JSON validator. It is also sound as an abstract `wasmFun` export acceptor and for the JSON `Format`. Partial correctness: termination is not proved. |
| `Silmaril.Wasm.Abstract.Accept.{Defs,Thms}` | First-class acceptor sets of abstract modules and components (`Silmaril.Games.Abstract`). On trace models and machines: `tmAccepted`/`mAccepted`, the one-runner verdicts `tmAcceptsSome`/`tmNeverRejects`/`tmAcceptsSafely`, and `tmIndexed`. On abstract functions: the export verdicts `retAccepts*` over `endRun`, the import reading `callAccepted`, and the per-invocation relation `callRel`. A machine and its denotation agree on Proponent observations. Monotone/antitone one-sided verdicts, bisimulation and `ObsEquiv` invariance. |
| `Silmaril.Wasm.Abstract.AcceptWasm.{Defs,Thms}` | Exact commuting diagrams for the abstraction maps on main. `wasmFun`: abstract endings map onto Core `behaviours`, so export verdicts on behaviour-defined sets commute. Scalar instances (`machine`) and untyped instances (`uMachine`): concrete strategy acceptance = abstract machine acceptance for Proponent observations. Not related: spec sessions (`Callouts`) vs instance strategies. |
| `Silmaril.Wasi.Component.Accept.Abstract.Thms` | Components through `SigBridge.strategyIso`. Every import/export, rejection and combined verdict is the abstract one on the trace model, exactly; refinement transports through the isomorphism. |
| `Silmaril.Wasm.Component.Reference.WIT.Repr.Func.Thms` | A WIT representation is a one-to-one relation (`Silmaril.Accept.OneToOne`, #270), and so is its inverse: the relational form of a Lean type being isomorphic to a WIT type. |
| `Silmaril.Wasm.Component.Reference.WIT.JsonDecide.Thms` | The JSON decider (#266) is exact for the JSON byte language. The language is infinite (proved), so no one-call module acceptor is complete for JSON (`ModuleAcceptor.not_complete_json`, unconditional). A `StreamCorrect` component with JSON as its specification answers each stream prefix by JSON validity. |
| `Silmaril.Wasi.Component.Accept.Stream.Monitor.Thms` | Incremental components as monitors of chunk streams (#258). A correct component's answer after the first `n` chunks is `decide (cs.prefixAt n ∈ L)`. Given answers for every `n`, the safety verdict `Chunks.AlwaysAt L cs` holds iff they are all `true`. The answers are a hypothesis: answering is liveness, outside the model. |
| `Silmaril.Wasm.Component.Reference.WIT.Json.Thms` | JSON (#261) as WIT inputs. JSON is a subset of UTF-8, and the JSON texts are exactly the UTF-8 encodings of `jsonStrings` (`utf8_jsonStrings`, `exact_json_iff`). JSONL-shaped item lists are `everyItem` (#275), carried as `list<list<u8>>`, and per-item bounds transfer. One-call modules are complete for no infinite JSON language (infinitude is a hypothesis). Byte-level JSON Lines delimiting is not modelled. |
| `Silmaril.Wasm.Game.Accept.Strict.Thms` | "Some run accepts and no run rejects" for modules is `Silmaril.Accept.acceptsSafely` (#296) of one runner (`moduleRun`: the same profile, environments and memory for both quantifiers). Values with no callout are not accepted, though they are never rejected. Invariance under callout equivalence. It is not monotone in the environment class. |
| `Silmaril.Wasi.Component.Accept.Strict.{Defs,Thms,Examples}` | The same for components, exported (`true`/`false` returns) and imported (`accept` called / `reject` never called), as `acceptsSafely` of one runner over the plays of one strategy. Invariant under equal traces and `CompEquiv`. The verdict components have combined language `A \ R`. Cases: accept only, reject only, both on different plays, no outcome, `⊥`, and pending (unanswered) calls. Refinement is neither monotone nor antitone, by counterexample. |
| `Silmaril.Formats.Accept.Stream.Thms` | `ChunkView` instances for `KBytes` and `Formats.Bytes`; on every bytes-like type a chunk's symbols are its bytes. `ByteLang.toStream` is a byte language as a `Silmaril.Streams.Lang` (#252) of finite words only. |
| `Silmaril.Wasi.Component.Accept.Stream.{Defs,Thms}` | Incremental components with exports `process(list<u8>)`, `query() -> bool` and `reset()`, after `Silmaril.Semantics.Acceptors` (#255). `StreamCorrect` requires every given answer to be the `specObs` answer, for inputs of any length. It is a safety property (`⊥` is correct), is preserved by refinement, and is invariant under traces and `CompEquiv`. `answer_eq_member` gives the answer after processing `w`. Whether an answer is given at all is liveness, outside the model. |
| `Silmaril.Wasm.Component.Reference.WIT.Utf8.Thms` | WIT `string` and the UTF-8 language of `Silmaril.Formats.Utf8` (#254). Every string acceptor's byte language is sound for UTF-8, and the byte language of all strings is exactly the UTF-8 language. Only the `utf8` string encoding is covered. |
| `Silmaril.Formats.Accept.Bounded.{Defs,Thms}` | Set-level `SoundWithin`, `CompleteWithin` and `ExactWithin` on a domain `D` (a length, depth or per-item bound, via `Silmaril.Accept.within`). They agree with the checker forms `SoundOn` and `CompleteOn`, and transport along injective encodings. A finite acceptor set is complete for no infinite specification. |
| `Silmaril.Wasm.Component.Reference.WIT.Repr.{Defs,Thms,Examples}` | `Repr E α t := α ≃ t.Interp E` represents a Lean type by a WIT type. Combinators: primitives, `list<u8>`, `list`, `option`, `tuple`, `result`, two-case `variant`, `stream` (`list<event>`) and `items` (`list<list<u8>>`). A WIT acceptor is sound, complete or complete-within-a-bound for a represented specification iff its Lean pullback is. These are representation bridges only. Event validity (brackets, number lexemes, CBOR tags, indefinite lengths, numeric profiles) belongs to the format's specification. |
| `Silmaril.Wasi.Component.Accept.Repr.Thms` | `reprLang r σ f` and `exportReprLang` are the Lean values whose WIT representation a component accepts. Soundness, completeness and bounded completeness bridges hold, with invariance under traces and `CompEquiv`; at `list<u8>` this is `bytesLang`. |
| `Silmaril.Wasm.Game.Accept.Complete.{Thms,Examples}` | A one-call `accept(ptr, len)` module acceptor is complete for no infinite specification (its language is finite). At best it is complete within the interface bound (`< addrBound`), and soundness only needs checking there. This covers the one-call interface only: multi-call or streaming modules are not covered, and unbounded streaming completeness is not claimed impossible. |
| `Silmaril.Formats.Accept.Bounds.Thms` | `Finite UInt8`. A byte language with a length bound is finite. Size slices (`Silmaril.Accept.upTo List.length n`) are finite, and a language whose strings are all `≤ n` long is its own slice at `n`. |
| `Silmaril.Wasm.Game.Accept.Bounds.Thms` | Exact module bounds. The `i32` encoding gives `< 2^32` (`≤ 2^32 - 1`), and `memory64` gives `< 2^64`. Separately, `ptr + len ≤ memory size`; for a 65536-page memory this alone would allow `2^32` bytes. Zero length: `accept(ptr, 0)` observes `[]` iff `ptr ≤ size`. The decoder is complete. Every module byte language is finite. |
| `Silmaril.Wasm.Game.Accept.Reject.{Defs,Thms}` | `rejected` and `neverRejected` (the latter is `Silmaril.Accept.neverRejects` of the rejecting callouts, and is antitone in the environments). `acceptedNotRejected`. `Calls`: callouts with their import index. `indexed`: an `IndexedLang` per index, whose erasure is acceptance through any import. |
| `Silmaril.Wasi.Component.Accept.Reject.{Defs,Thms}` | `neverCalled` (an import `reject(v)` is never called) and `neverFalse` (an export `reject(v) -> bool` never returns `false`). Both are safety properties that hold vacuously (`⊥` never-rejects everything), grow under refinement, and are invariant under equal traces and `CompEquiv`. Indexed sets by WIT name (`importIndexed`) and by layout position (`layoutIndexed`). |
| `Silmaril.Wasi.Component.Accept.Bounds.{Defs,Thms,Examples}` | Component bounds hold only under explicit canonical-ABI assumptions. `CanonLowerAcceptBy obs` gives `< 2^32` (32-bit memory) or `< 2^64` (`memory64`). `ListLiftChecked lim` (the `listTooLong` check) gives `≤ lim.maxListBytes`: `2^28 - 1` under `Limits.spec`, `2^32 - 1` under `Limits.wasmtime`. Without an assumption, the component accepting all byte strings has an infinite language. |
| `Silmaril.Wasm.Game.Accept.Acceptor`, `Silmaril.Wasi.Component.Accept.Acceptor.{Defs,Thms,Examples,Quot}` | Wrappers. `ModuleAcceptor` bundles a module with its `accept`/`reject` imports, memory, address width and environments. `ComponentAcceptor` bundles a model with `accept`/`reject` and an import or export `Mode`, and `ofIR` builds one from an IR component. `ByteAcceptor` is the sum of the two (`Silmaril.Accept.langSum`). All are CSLib `Acceptor`s. `CanonPair` relates a module and a component: they accept the same language and lie in one `LangEq` class. Semantic setoids (`calloutSetoid`, `traceSetoid`) respect every language. |

## Assumptions and scope

- **Existential reading.** An input is accepted when *some* run, against *some* admitted
  environment, observes it. Strategies are receptive, so their plays range over every
  environment. Acceptance is a may (safety) property: divergence or a trap after the call
  does not matter.
- **Module environments.** By default `Envs` is `UEnvOk`, Core's host contract: a typed store
  that extends the caller's, and a typed result. The Wasm specification lets a host change
  memory contents, so once any import has been called the memory can hold anything. Smaller
  environment classes give smaller sets (`callouts_mono`). Only modules whose imports are all
  functions are covered (`IsSpecInstance`).
- **Floats** are interpreted as IEEE bit patterns (`BitVec 32/64`). The reference ABI may
  canonicalise NaNs, so float acceptors relate to it only up to that canonicalisation.
- **Handles.** The interpretation names handles: by table index in the canonical ABI and
  WASI encodings, by representation (`Value.Val`), or by an abstract carrier. Ownership and
  borrow lifetimes are trace properties and are not checked by the types.
- **Recursive types.** WIT type definitions are acyclic, and the only recursion goes through
  resources, which the interpretation reaches only through handles. The repository's WIT
  types have no recursive form. Names (`ref`) are interpreted by the environment.
- **Not proved: module/component correspondence.** The IR components have no list values and
  no memory lowering, and the reference canonical ABI has no trace semantics. So
  `CanonLowerAccept` is a hypothesis: no adapter is proved to satisfy it. What is proved:
  - the core signatures `(i32, i32) -> ()`, `(i64, i64) -> ()` and `(i32, i32) -> i32`;
  - the size and alignment `1` of `u8`;
  - that `Callout.bytes32` reads exactly the contiguous segment `[ptr, ptr + len)`, element
    by element (`getElem?_of_segment`).
- **Tests.**
  - Kernel-checked decoder runs, for both the module and the WASI decoders.
  - Non-vacuity on a real module: `exStart`'s start function calls its import, and that call
    is a reachable callout for every profile.
  - `bytesLang (importAcceptor L run) = L`.

- **Bounds: `<` versus `≤`.**
  - Address-width bounds are strict, from fixed-width integers: `< 2^32` for `i32`, `< 2^64`
    for `i64`.
  - Canonical-ABI lift checks are non-strict, since they compare with a maximum:
    `≤ MAX_LIST_BYTE_LENGTH`.
  - The memory's own size gives `ptr + len ≤ size`.
- **Component bounds are hypotheses.** No adapter is proved to satisfy `CanonLowerAcceptBy`
  or `ListLiftChecked`.

## I/O relations of modules

`Callouts` is a set read off a reachability predicate, so it forgets which callouts happen in
which export invocation, in which order, and which host answer was the input.
`Silmaril.Wasm.Game.IOAccept` keeps that information:

- `TSession P L m memAddr R c₀ q₀ addrs p w x ts` has the constructors of `Session` (a
  host-free step, a host answer, an invocation) plus `call` (tag the callout at a host-call
  redex, once) and `ret` (tag the end of an invocation). Tags: `enter (entry a args)` at an
  invocation; `inp (callIn o)` then `out (callOut o)` at a callout `o`; `inp (answerIn o w)`
  at the host's answer, where `w` holds the raw `Result` and the memory bytes after the
  answer (`UStep.answer` exposes the reply, so nothing is parameterised beyond the decoders);
  `exit (result vs mem)` for returned values, `exit none` for a trap or uncaught exception.
- Erasure: `TSession.toSession` and `Session.exists_tsession`; hence `callouts_eq_traced`.
  Traced acceptance refines `Callouts`: every output of a run is the `callOut` of a reachable
  callout (`exists_callout_of_mem_ioRuns`, `exists_callout_of_mem_entryIORuns`), every window
  input is read off one (`exists_callout_of_input_ioRuns`), and with
  `callOut = outputVia imp dec` a triggered output is in `accepted dec … imp m`
  (`mem_accepted_of_mem_triggers`). Monotone in `Envs` (`ioRuns_mono`, `entryIORuns_mono`).
- Example: `exStart`'s export `"run"` triggers its call of `"env" "f"`
  (`(1, ("env", "f")) ∈ triggers (entryIORuns P UEnvOk 0 exStart runRoles)`), while the same
  call made by the start function is outside every scope.

Limitations:

- **Internal outputs outside any invocation.** Callouts of the instantiation phase (segment
  initialisation, start function) come before any `enter` and are dropped by `bracket`
  (`TSession.bracket_eq`); they remain `Callouts` (and so `accepted`) but trigger nothing.
- **No reentrancy.** The environment invokes exports only after a run has finished, and a host
  answer is a single relation step, so a host call cannot call back into the module; traced
  sessions are flat (`TSession.openScan_eq`). Reentrant hosts need another semantics.
- **Untagged calls.** A redex whose host code is not an import index (a host function added by
  the environment and called by reference) is not a `CalloutOf` and is not tagged. A host
  divergence (`UStep.silent`) is a self-loop and adds no tag.
- **Reading order of a call.** A call that is both an input and an output is tagged input
  first, so its own input triggers its output; another causal structure needs other roles.
- **Finite prefixes.** Runs of an unfinished invocation have result `none`; divergence is not
  observed.
- Only modules whose imports are all functions (`IsSpecInstance`), as for `Callouts`.

## Checking

```
lake build --wfail Silmaril.Formats.Accept.Examples Silmaril.Games.Accept.Thms \
  Silmaril.Wasm.Component.Reference.WIT.Interp.Examples Silmaril.Wasm.Game.Accept.Examples \
  Silmaril.Wasi.Component.Accept.Examples Silmaril.Wasi.Component.Accept.Canon.Thms \
  Silmaril.Wasm.Game.IOAccept.Examples
```
