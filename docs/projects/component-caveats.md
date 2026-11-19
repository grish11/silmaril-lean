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
| an interface (game) denotation of REF components whose plays include **host-function calls** | **missing** (the bridge item 1 means) | REF has an *operational* reading of import calls: `Ref.Accepted`/`AcceptedTyped` observe the host function's arguments in machine runs. The *denotational* side is missing: no map from a REF component to a strategy `Strategy (nsig I) (nsig X)` (a WASI world model, `Layout.compModel`'s codomain) in which a call of a host function is a P-move with its lifted arguments. REF→strategy exists only for import-free `Simple` components (`SessionAdequacy`, `SessionStrat` in review) | define `refModel c : L.world.Model` from REF sessions with host calls, and prove adequacy `AcceptedTypedBytes ft prof c w ↔ w ∈ bytesLang (refModel c) acceptFn` |
| tuple-acceptor bridge (REF ↔ IR on the fragment both read) | **partly done**: prerequisites exposed | `tupleHiBytes` is read by both (kernel); REF passes `accept` a record, so the `list<u8>` notion is empty on it and `AcceptedTypedBytes` (through `bytesOf?`, the IR's `bytes?` reading) is needed; the host must be linked at the component's import type (`acceptLinkedProgAt`); the tuple acceptance is **kernel-checked end to end** (`tupleHi_accepts`) | (P2) `bytesOf? [toRefVal v] = args1 bytes? [v]` on IR values; (P3) an execution-based `CoreSem CoreMod` for lowered core modules (the library has only `topSem`, under which the IR side is not about the core code); (P4) REF↔IR adequacy with imports (`Simple.sound` is import-free). Then `AcceptedTypedBytes ft prof (decodeRef b) w ↔ w ∈ (ComponentAcceptor.ofComp C (lower b)).lang` |
| REF↔IR adequacy beyond `Simple` | **missing** | `Reference.Sound` (`Simple.sound`, numeric, import-free) | (P4) above |
| `RefSimple.ofRef?` (bytes → `Simple`) linked to the acceptor APIs | **unwired** | `JcoTool.RefSimple` | use it to check the two paths agree on scalar components |
| real Core 3.0 instances for the jco wrapper model (`Jco.Real.realInst`) linked to REF | **unwired** | `Jco.Real.Inst`, `Jco.Wrap` (`wrap_correct` for strings and `list<u8>` exports, relational) | prove that REF runs the `wrap md` component of a real module as `md.spec` |

## Verification gaps

| item | status | evidence | next step |
|---|---|---|---|
| end-to-end runs with linear memory are not kernel-checked | **gap** | evaluating a 64 KiB memory in the kernel exceeds its recursion depth (`decide +kernel` fails); the run is checked by `#guard` and enters proofs only as a hypothesis (`hi_mem_of_runHi`) | kernel-friendly memory representations (the `Wasm.KernelEval` work in review) |
| no proof that a REF component accepts *only* certain bytes | **gap** | `Accepted` is existential; only inclusions are shown | invariants of REF runs (e.g. a component that never calls `accept` accepts nothing) |
| upstream parity suites (wasm-tools, jco, wac, wasmtime) | **gap** | not run by CI (`docs/projects/wasm-components.md`) | run them in a scheduled job |

## Instantiation and start functions in the component IR

| item | status | evidence | next step |
|---|---|---|---|
| start functions run at instantiation, in program order; a start trap aborts the instantiation | **unwired** (IR denotation and Core 3.0 engine instance; the acceptor and consequence APIs still use the start-free `Comp.denU`) | `InstSem`: `CoreSemI` (instantiation question `inst` before export calls), `Comp.denI` (nodes instantiated in order by `extI`; the first failure is the answer and later nodes are never asked; the protocol guard `instGuard`); `denIR_toI`, `denI_toI_iff`: for start-free `C`, `denI C.toI` after `[inst, ready]` is exactly `Comp.denU C`. `InstEngine`: `engineSemI`, `core3SemI P` (start function at `inst`, its import calls as moves, export phase `engineStrategy`). `InstLitmus` (Core 3.0, kernel-computed instances, `Step`-built runs): order of two start calls (`twoC_inst`, every profile; `twoC_order`, deterministic profiles), import call at instantiation (`oneC_inst`), start trap fails the instantiation, no later start runs, no export answers (`trapC_inst_fails`; `trapC_plays` and corollaries at deterministic profiles), never-called instance still started (`hiddenC_inst`) | relate `Comp.denI` over `core3SemI` to REF instantiation (`Reference.Instantiate`, `runStart`); use `Comp.denI` for lowered binaries (`Binary.coreModSem` is start-free) |
| the export phase of `engineSemI` is `engineStrategy` | **gap** (one inclusion) | `engineStrategyI_after_start`, `engineSemI_after_ready`: every `engineStrategy` play follows the instantiation play | prove the converse inclusion |
| divergence of a start function | **assumption** | strategies do not observe divergence: a diverging start phase leaves `inst` unanswered (`Silmaril.Wasm.Game.Start` observes it with `DStrategy`) | a divergence-observing `Comp.denI` |

The opt-in *lazy* start semantics proposed separately (start function run at the first export
call) is not the specification's and is not used here.

## Assumptions of `Ref.Accepted` and the typed environment

* **Host.** The host's `accept` is synchronous: it records its arguments and returns no result.
  It is REF's `mk_host_func` pattern. `acceptLinkedProgAt ft` supplies it at type `ft`, and
  REF's import check makes `ft` the component's import type.
* **Untyped environment (`Accepted`, `EnvLabel`): spurious runs.** Invoking an export on
  arguments that do not have its WIT type violates REF's precondition. Usually the machine
  stops with an `internal` fault, but not always: the exported `len == 3` acceptor returns
  `true` on the ill-typed list `[u32 300, u8 1, u8 2]` (`Ref/Typed/Examples.lean`, `#guard`).
* **Typed environment (`AcceptedTyped`, `TypedEnvLabel`), the intended semantics.** The host
  invokes exported functions only on arguments of their WIT type (`Val.HasType`, checked by
  the kernel-reducible `Val.typeCheckList?`), ticks and cancels. `AcceptedTyped → Accepted`,
  and `refTypedBytesSystem ≤ refBytesSystem`. The typed driver refuses ill-typed calls, as the
  tests show. Making the typed notions the default (replacing the untyped `refBytesSystem`) is
  a reviewer decision; both are kept for now.
* **Re-exported `accept`: intended.** A component that re-exports its `accept` import lets a
  typed host call `accept` through it, so it accepts every byte string the host passes. The
  IR reading (`Wasi.Accept.bytesLang`, import calls in plays of the wiring) counts these calls
  too. It is a property of the component's interface, not an ill-typed host (`#guard` test).
* **Validation and engine.** `refBytesSystem` validates at `Features.p2` and runs over the
  executable Core 3.0 engine `core3 neverFail`. `Accepted` itself holds for any core engine
  and any component choice profile.

## Streams, async and jco

Streams, futures, async lifting and lowering, the stream transformer algebra and the jco-style
toolchain are present (`Silmaril.Wasm.Component.Streams`, `Silmaril.Wasm.Component.Async`,
`Silmaril.Wasm.Jco`, `Silmaril.Wasm.JcoTool`, the REF runtime `Reference.Runtime.Stream*`).
Module names below are relative to `Silmaril.Wasm`.

| item | status | evidence | next step |
|---|---|---|---|
| a concrete stream semantics for generated modules | **done** for generated modules; a general one is **refuted** | `JcoTool.KReadComp.gen_realizes`: a well-formed generated module (`CoreGen.OK`) on Core 3.0 realises its kernel's transformer `trV k` in the stream game (`gen_seq`, `gen_equiv_compose` for plugging); `JcoTool.KRead.core_game`: the Core runtime's strategy is `StreamGame.den (trV k)`. `Component.Algebra.StreamSem.not_faithful`: no `StreamSem` over arbitrary item types is faithful, so `StreamGame.den` is over `Val` items | none (the `Algebra.Pipe` docstring "none is constructed here" predates `StreamGame`) |
| emitted binaries and the transformer models | **wired**, with stated hypotheses | bytes to module: `JcoTool.KCoreEmit` (`wasmOf_encodes`, `kcore_new`), `JcoTool.KDropEmit.kdrop_tool_correct`; module to model on Core 3.0: `JcoTool.KCoreRun`, `JcoTool.KRead.core_whole_correct`, `JcoTool.KDrop.kchain_correct`, `JcoTool.KTeeCore` | the hypotheses: validity of `genD k N` and `toModuleT N` for every `k`, `N` (checked by `validate?` and `wat-cert.sh`, not proved); network start states taken from the setup store, not from running the lifts; the deterministic profile, injective host-call encodings and well-formed runtime events (`wfD`); the tee's backward Core-to-model step is missing |
| `DROPPED` events of the `Async` store model | **gap**, characterised | `Component.Async` posts `DROPPED 0` only to a peer with a pending copy. Kernel-checked differences from the transcription of `definitions.py` (`Component.Async.Cabi`, `dropEnd_notifies_idle`, `deliverEnd_dropped`): `CabiAgree.differ_idleDrop` (an idle peer is notified), `differ_eventAtDelivery` (`DROPPED` with the count when the writer drops before the reader's event is taken), `differ_afterDropped` (a copy after `DROPPED` traps), `differ_futureDropW`. Agreement with drops is bounded and guarded: `CabiAgree2.agree_streamDrops`, `agree_futureDrops` (traces of at most 4 operations satisfying `guardOk`), `unguarded_differ` (the guard is needed). `Component.Streams.Drop`, `Cancel` and `ACancel` implement the drop-faithful semantics and carry `JcoTool.KDrop`, `KTee`, `KLive`, `KNetCore` | relate `Streams.Drop`/`ACancel` to `Async.Cabi` (no theorem does; `Drop` is checked against wasmtime tests only); move the users still on `Async` (`Streams.Proc`, `JcoTool.StreamSem`, `JcoTool.KCore`, WASI 0.3, `Jco.Async`) to `Drop` |
| jco adaptor against Core 3.0: `memory.copy`, `if … else … end`, integer stores | **done** for well-typed code, under two hypotheses on the wrapped instance | `Jco.Real.StepX.execT_agree`, `invokeT_agree`: a returned run of adaptor code accepted by the type checker `tyExec` (stack and local types; `if` branches typed from an empty stack) is a reference-semantics run of its Core 3.0 image. Core's byte-by-byte `memory.copy` computes the abstract `memmove` (`Proofs.Wasm.Jco.Real.Copy.core_copy`); an `if` branch runs on an empty operand stack inside its block's label (`Proofs.Wasm.Jco.Real.Framing.exec_frame`). Hypotheses: `CallsTyped` (calls return values of the declared result types), `MemOk` (the memory has at most `2^32` bytes) and `CallsKeepMem` (calls keep `MemOk`) | derive `CallsTyped` and `CallsKeepMem` from Core 3.0 type soundness and the 32-bit memory limit |
| the `cabi_realloc` of the `utf16` and `latin1+utf16` wrappers on Core 3.0 | **done** | `Jco.Real.StepX.reallocShimX_core`: when `alloc` returns one `i32`, the Core 3.0 image of `reallocShimX` (`if`, `select`, `memory.copy`) returns what `reallocEmu` returns (allocate, then copy `min(old_size, new_size)` bytes); `reallocShimX_typed` | none |
| jco adaptor against Core 3.0: float loads and stores | **missing** | outside `tyStep` (`Jco.Real.StepX.Defs`) | add them to `tyStep` with `n = width / 8` (the multi-value shim `mvShim` stores floats) |
| jco adaptor against Core 3.0: traps | **done** for well-typed code, under one more hypothesis on the wrapped instance | `Jco.Real.StepX.execT_trap`, `invokeT_trap`, `reallocShimX_core_trap`: a trapping run of well-typed adaptor code is matched by a Core 3.0 run that reaches `trap` (out-of-bounds `memory.copy`, loads and stores trap as in Wasm; an `if` branch's trap leaves its label). Hypothesis `CallsTrapCore`: a trap of a call of the wrapped instance is a Core trap. `realInst` also reads uncaught exceptions, ill-typed invocations and non-flat results as traps (`Jco.Real.Inst`), and these are not Core traps | discharge `CallsTrapCore` for exception-free modules with number-typed exports (validation and type soundness) |
| `utf16` and `latin1+utf16` transcoding against `definitions.py` | **restated**, not proved | `Jco.Styles.Enc` restates `store_utf8_to_utf16`, `store_string_to_latin1_or_utf16` and `load_string_from_range` (`a25fc0b`) over the instance's memory and an arbitrary `realloc`; its length bound is `2^31 - 1`, the reference's `MAX_STRING_BYTE_LENGTH` is `2^28 - 1`. REF transcribes the same functions separately (`Component.Reference.ABI.String`) | prove `Enc`'s stores and loads equal to `Reference.ABI.String`'s on a shared memory and `realloc` |
| memories, tables and canonical options shared across instances | **REF only** | REF has the canonical options per lift and lower (`Component.Reference.Runtime.Options.CanonOpts`: `string-encoding`, `memory`, `realloc`; `CanonOpts.liftEqual`). Simplified away elsewhere: `Component.Async` (one handle table), `Component.Async.Cabi` (per-instance cell memory, no `realloc` or `post-return`), `Component.Streams.Drop`, `Cancel`, `ACancel` (no same-instance trap of `End.copy`), `Jco.Async.Lower` (no transfer of ends between per-instance tables), `Component.Binary.Lower` (`string-encoding`, `memory`, `realloc` ignored); the jco wrappers have one wrapped instance whose memory every lift uses | a lowering that keeps the options and per-instance tables, with an agreement theorem against REF |

See `docs/projects/wasm-components.md`.
