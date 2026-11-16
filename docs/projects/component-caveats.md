# Wasm components: caveat ledger

What the component developments cover today, ordered by how much they block giving meaning to
real component binaries. Each entry gives the evidence and the next step. Status words:
**wired** (implemented and connected to the public acceptor and consequence APIs),
**unwired** (implemented but not connected), **missing**, **assumption** (a modelling choice)
and **gap** (a verification gap).

## Acceptance of component binaries

| item | status | evidence | next step |
|---|---|---|---|
| `accept(list<u8>)` binaries have meaning, imported or exported `accept` | **wired** on the reference machine (REF) | `Silmaril.Wasi.Accept.Ref`: `Accepted`, `refBytesSystem`, `acceptRun_sound`; `Ref/Examples.lean` decodes and validates a real `accept(list<u8>)` binary in the kernel and runs it (`#guard`), recording `"hi!"`; `AcceptedExport` (REF `exportBehaviours`) for `accept: func(list<u8>) -> bool`, with `#guard`ed runs returning `true`/`false` | see the gaps below; the exported form covers components without root imports, one call after instantiation |
| the component IR reads lists, strings, flags, resources | **missing** | `Binary/Lower/Defs.lean`: `defValTy` rejects them; the IR's `ValTy` has no list type | extend the IR's ABI with linear memory, or keep REF as the semantics of such components |
| REF trace (game) semantics with imports, as a WASI world model | **missing** | REF→strategy covers import-free `Simple` components only (`Reference.SessionAdequacy`, `SessionStrat` in review) | define REF sessions with host calls; relate `Ref.Accepted` to `Wasi.Accept.bytesLang` on components both read |
| REF↔IR adequacy beyond `Simple` | **missing** | `Reference.Sound` (`Simple.sound`, numeric, import-free) | extend to imports and tuples, then prove `Ref.Accepted = ComponentAcceptor.lang` on tuple acceptors |
| `RefSimple.ofRef?` (bytes → `Simple`) linked to the acceptor APIs | **unwired** | `JcoTool.RefSimple` | use it to check the two paths agree on scalar components |
| real Core 3.0 instances for the jco wrapper model (`Jco.Real.realInst`) linked to REF | **unwired** | `Jco.Real.Inst`, `Jco.Wrap` (`wrap_correct` for strings and `list<u8>` exports, relational) | prove that REF runs the `wrap md` component of a real module as `md.spec` |

## Verification gaps

| item | status | evidence | next step |
|---|---|---|---|
| end-to-end runs with linear memory are not kernel-checked | **gap** | evaluating a 64 KiB memory in the kernel exceeds its recursion depth (`decide +kernel` fails); the run is checked by `#guard` and enters proofs only as a hypothesis (`hi_mem_of_runHi`) | kernel-friendly memory representations (the `Wasm.KernelEval` work in review) |
| no proof that a REF component accepts *only* certain bytes | **gap** | `Accepted` is existential; only inclusions are shown | invariants of REF runs (e.g. a component that never calls `accept` accepts nothing) |
| upstream parity suites (wasm-tools, jco, wac, wasmtime) | **gap** | not run by CI (`docs/projects/wasm-components.md`) | run them in a scheduled job |

## Assumptions of `Ref.Accepted`

* **Host.** The host's `accept` is synchronous: it records its arguments and returns no result.
  It is REF's `mk_host_func` pattern.
* **Environment.** After instantiation the host invokes exported functions on arbitrary
  arguments (they are not type-checked by the model), ticks, and cancels calls. It runs no
  other host program. A component that re-exports `accept` therefore accepts every byte string.
* **Validation and engine.** `refBytesSystem` validates at `Features.p2` and runs over the
  executable Core 3.0 engine `core3 neverFail`. `Accepted` itself holds for any core engine
  and any component choice profile.

## Streams, async and jco

Streams, futures, async lifting and lowering, the stream transformer algebra and the jco-style
toolchain are present (`Silmaril.Wasm.Component.Streams`, `Silmaril.Wasm.Jco`,
`Silmaril.Wasm.JcoTool`, the REF runtime `Reference.Runtime.Stream*`). These items are open:

* a concrete stream semantics (`StreamSem`) for generated modules;
* the link between generated or emitted binaries and the transformer models;
* the `DROPPED`-event gap of the `Async` model;
* parts of the jco adaptor against Core 3.0: stores, `memory.copy`, `if`, traps, and
  `latin1+utf16`.

See `docs/projects/wasm-components.md`.
