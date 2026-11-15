# Accepted inputs: byte languages, modules and components

What does a WebAssembly module or component *accept*? This development defines the set of
inputs a program accepts, as a language. It reuses the repository's Wasm and WIT semantics
and equivalences, and keeps every assumption explicit.

## Modules

| Module | Contents |
| --- | --- |
| `Silmaril.Formats.Accept.{Defs,Thms,Examples}` | Acceptor sets `Lang α := Set α`; `Sound` (`A ⊆ S`), `Complete` (`S ⊆ A`), `Exact`; transport along encodings and decodings. `ByteLang := Language UInt8` (Mathlib). `BytesLike` covers `List UInt8`, `Array UInt8`, `ByteArray`, `KBytes` (with `KBytes.ofList` for the lawful instance) and `Formats.Bytes`; membership is `b ∈ᴮ L` (`ByteLang.Accepts`). Soundness and completeness are closed under `+`, `*` and `∗`. Byte languages are CSLib `Acceptor`s. Examples use a Mathlib `DFA` over bytes. |
| `Silmaril.Games.Accept.{Defs,Thms}` | Acceptance over any trace model or strategy (`observed`, `Strategy.accepted`). It is monotone in refinement. Observable-trace equivalence (`ObsEquiv`) preserves it, and so do move maps that commute with the observation. A generated strategy accepts exactly what its generating plays observe (`accepted_generate`). |
| `Silmaril.Wasm.Component.Reference.WIT.Interp.{Defs,Thms,Examples}` | Simple WIT types: the existing `WIT.ValType` with no `future` or `stream` (`ValType.simple`, `SimpleType`). `ValType.Interp E t` interprets them as Lean types (`u32 ↦ UInt32`, `s64 ↦ Int64`, `list ↦ List`, records ↦ products, variants ↦ sums, `flags ↦ BitVec n`, …); handles and names come from an environment `Env`. `ValLang E t` is the acceptor set at a type; `list<u8>` acceptors are definitionally byte languages; UTF-8 transports string acceptors faithfully. The canonical-ABI core signatures of the `accept` functions (`flattenFunc_accept_*`) and `layout_u8` are here too. |
| `Silmaril.Wasm.Game.Accept.{Defs,Thms,Examples}` | Core modules: `Callouts P Envs memIdx m` is the set of reachable import calls. A call records the import's name, its arguments and the bytes of memory `memIdx` at the call. Calls are collected after the specification's instantiation (`IsSpecInstance`), in sessions of the untyped game semantics (`UStep`) against every environment of the class `Envs`, which may also invoke exports with typed arguments. Accepted values come from decoders: `bytesLang` (`accept(ptr: i32, len: i32)`), `bytes64Lang` (memory64), `i32Lang` and `i64Lang`. `CalloutEquiv` is exactly the equivalence under which every decoder accepts the same values (`calloutEquiv_iff`). |
| `Silmaril.Wasi.Component.Accept.{Defs,Thms,Examples}` | Components as WASI world models (`Strategy (nsig I) (nsig X)`, named events `WEv`). `bytesLang σ f` covers an imported `accept: func(list<u8>)`; `exportBytesLang σ f` covers an exported `accept: func(list<u8>) -> bool` that may return `true`. `valLang` and `exportValLang` do the same at any closed WIT type, through a strict decoder (`decode`) that follows the WASI value encodings. Acceptance is invariant under equality of named traces, monotone in refinement, and `CompEquiv` / `CompRefines` IR components (under any `Layout`) have equal / included acceptor sets. Every byte language is exactly accepted by a specification component (`importAcceptor`, `exportAcceptor`). |
| `Silmaril.Wasi.Component.Accept.Canon.{Defs,Thms}` | `CanonLowerAccept`: the correspondence a canonical-ABI adapter must establish between a module's `accept(ptr, len)` callouts and a component's `accept(list<u8>)` calls. Given it, the two byte languages are equal. |

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

## Checking

```
lake build --wfail Silmaril.Formats.Accept.Examples Silmaril.Games.Accept.Thms \
  Silmaril.Wasm.Component.Reference.WIT.Interp.Examples Silmaril.Wasm.Game.Accept.Examples \
  Silmaril.Wasi.Component.Accept.Examples Silmaril.Wasi.Component.Accept.Canon.Thms
```
