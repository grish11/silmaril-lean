# SQLite Progress-Handler and Interrupt Liveness: Proof-Design Note

**Status:** Defensively scoped proof-design and source-audit note. All Lean definitions, theorem statements, and trace sketches below are **UNCOMPILED** (design sketches only; no Lean build or native runtime test was run). No exploit development, reproduction programs, or payloads appear in this document.

### Epistemic Labels Used Throughout

Every claim in this note is tagged by evidence boundary:

- **`[Doc]`** — Stated in official `sqlite.org` API/security documentation (`progress_handler.html`, `interrupt.html`, `security.html`).
- **`[Source-only]`** — Inferred strictly from static inspection of pinned SQLite 3.54.1 source (`sqlite3.c`, `sqlite3.h`) and build metadata (`corpus/sqlite/package.toml`); **no runtime execution, dynamic test, or compiled ELF binary inspection was performed**.
- **`[Abstract-VM target]`** — Proposed formal property for a high-level checked Lean VM model.
- **`[Open gap]`** — Unverified obligation or concrete discrepancy blocking any claim about real native SQLite.

---

## 1. Executive Decision & Explicit Non-Claims

**Decision:** Keep cancellation liveness and bounded response **strictly orthogonal** to existing universal finite-prefix safety (`Silmaril.Machine.SQLite.VirtualMachine.Isolation`, [Defs](../../Silmaril/Machine/SQLite/VirtualMachine/Isolation/Defs.lean), [Thms](../../Silmaril/Machine/SQLite/VirtualMachine/Isolation/Thms.lean)). Model responsiveness in a separate module quantified universally over **all** raw inputs under the configured profile — with **no** `Admitted`, `WellFormed`, `Terminating`, or "all runs reach a checkpoint" input premise.

### Explicit Non-Claims

1. **No unconditional termination claim:** Neither the abstract VM target nor SQLite asserts that arbitrary SQL or raw bytecode terminates without cancellation (`[Doc]`: [`security.html`](https://sqlite.org/security.html) §1.1 explicitly notes SQL can run "for a very long time" or "forever").
2. **No wall-clock or real-time guarantee:** Accounting units (abstract work ticks or SQLite's approximate VM-step counters) are **not** wall-clock milliseconds. Physical-time response bounds hold **only conditionally** when composed with independent OS scheduling, memory-visibility, CPU-step, VFS, busy-wait, mutex, and callback latency assumptions (`[Doc]`: SQLite docs make zero wall-clock promises).
3. **No bounded or interruptible write-rollback guarantee in real SQLite:** Once a write statement is interrupted, cleanup and rollback (`sqlite3VdbeHalt` / `sqlite3RollbackAll`) run **non-interruptibly** for transactional consistency `[Source-only]` and scale with uncommitted dirty pages, journal/WAL VFS I/O, virtual-table `xRollback`, and `xRollbackCallback`. Moreover, on the `[Source-only]` `OP_Halt` → `vdbe_return` path, `xProgress` returning non-zero after `sqlite3VdbeHalt` has already committed can still report `SQLITE_INTERRUPT` without rolling back. Do **not** conflate receiving `SQLITE_INTERRUPT` with bounded-time or guaranteed rollback without modeling these boundaries explicitly.
4. **No native `libsqlite3.so` verification claim:** Unmodified SQLite 3.54.1 has concrete `[Source-only]` checkpoint gaps across VDBE jump opcodes, prepare passes, single-opcode helpers, and busy-handler retry loops. Make **no blog-level claim** that native SQLite 3.54.1 satisfies the proposed abstract VM bounds until the internal implementation gap (Section 3) and C/TSO/ELF refinement layers (Section 8) are actually verified.

---

## 2. Grounded Source Inventory

### 2.1 Official SQLite Documentation (retrieved 2026-11-26)
- [Query Progress Callbacks (`sqlite3_progress_handler`)](https://sqlite.org/c3ref/progress_handler.html)
- [Interrupt A Long-Running Query (`sqlite3_interrupt`, `sqlite3_is_interrupted`)](https://sqlite.org/c3ref/interrupt.html)
- [Defense Against The Dark Arts (`security.html`, updated 2026-07-10)](https://sqlite.org/security.html)

### 2.2 Pinned SQLite 3.54.1 Amalgamation & Build Provenance
- Source ID: `2026-10-16 14:45:20 555e07ef33f69a0957d24d8e555b702464a131d6f1607f4c3c1e4551e8e6ca76`
- Official archive SHA-256: `0a9c8e34352dad46006aa82836d5383bff9dc6bc9ce5a60553c05aa30e6ad1f9` ([Corpus provenance](../../corpus/sqlite/package.toml))
- [`sqlite3.c`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c) (271,131 lines) — SHA-256: `0c657666d819f261cc4007526ad57e1669de9949df7a8ea847aa284a2bf0ee52`
- [`sqlite3.h`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.h) — SHA-256: `d6c84557261893439b341d2e6c35187ae3ea24fbfd843ad94616f72d89242b8c`
- Reference `libsqlite3.so` flags (`corpus/sqlite/package.toml`): `-O2 -g0 -ffile-prefix-map=/build/sqlite=. -DSQLITE_THREADSAFE=1 -MMD -fPIC` (defaults otherwise). `[Source-only]` build inferences: `SQLITE_OMIT_PROGRESS_CALLBACK` is unset (progress callbacks enabled), `SQLITE_ENABLE_API_ARMOR` is unset (armor checks omitted), and under GCC ≥ 4.7 `SQLITE_ATOMIC_INTRINSICS` evaluates to `1` (`__ATOMIC_RELAXED`, [`sqlite3.c#L15113-L15116`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L15113)). None of these were verified in the compiled ELF.

### 2.3 Existing Silmaril Abstractions Audited
- [VM Isolation Defs](../../Silmaril/Machine/SQLite/VirtualMachine/Isolation/Defs.lean) & [Thms](../../Silmaril/Machine/SQLite/VirtualMachine/Isolation/Thms.lean): universal finite-prefix safety over arbitrary `Vdbe.RawProgram` and `HostState`, with runtime `withinProfile` and `FallbackSafe`. Explicitly excludes parsing, preparation, cleanup, termination, step/memory caps, and C/ELF refinement.
- [Read-only VDBE core](../../Silmaril/Formats/Sqlite/Vdbe/Defs.lean), [VM Defs](../../Silmaril/Machine/SQLite/VirtualMachine/Defs.lean), [Mutable](../../Silmaril/Machine/SQLite/VirtualMachine/Mutable/Defs.lean), [Traced](../../Silmaril/Machine/SQLite/VirtualMachine/Traced/Defs.lean), and [Concurrent](../../Silmaril/Machine/SQLite/VirtualMachine/Concurrent/Defs.lean) (SC snapshot slot; explicitly omits mutexes, busy handlers, fairness, liveness).
- [File-control fragment](../../Silmaril/Machine/SqliteControl/Defs.lean) & [Confined lock release under SC/FIFO TSO](sqlite-confined-release.md).
- [Server Liveness](../../Silmaril/Servers/Live/Defs.lean): Silmaril's existing idiom for infinite traces (`ITrace`), weak fairness (`Fair`), and keeping safety separate from liveness.

---

## 3. Two Distinct Theorem Domains & Closing the Implementation Gap Internally

A central trap in formalizing cancellation liveness is confusing the **abstract checked VM domain** with the **real SQLite SQL/DB-byte domain** and smuggling the gap away as an input precondition. Keep these two domains strictly separate:

### Domain 1 — Abstract Checked VM over Arbitrary Raw Bytecode (`Vdbe.RawProgram`)
- **Quantification:** Universal over **all** `raw : Vdbe.RawProgram`, **all** `host : HostState`, and **all** configured `profile : Profile` — mirroring `VirtualMachine.Isolation` with zero input filter.
- **Why this works without an input filter:** The **abstract VM transition relation itself** enforces a certified inter-poll bound (`PollBound K`) internally on every execution step (e.g., via an internal work-tick countdown or polling on every backward edge plus a liveness-preserving fallback contract `FallbackLive`). Even an adversarial raw bytecode array containing tight self-loops hits a checkpoint within `≤ K` internal work ticks.

### Domain 2 — Real SQLite 3.54.1 over Arbitrary Raw SQL Text & Raw DB Bytes
- **Quantification target:** Universal over **all** raw SQL byte strings, **all** raw database file bytes (including corrupted pages/trees/overflow chains), and **all** modeled API call sequences under a configured SQLite profile (`sqlite3_limit(...)`, `DEFENSIVE`, `TRUSTED_SCHEMA=0`, etc.).
- **Why Domain 1 does NOT automatically transfer to Domain 2:** `[Source-only]` In unmodified SQLite 3.54.1, `sqlite3VdbeExec` does **not** poll on every jump opcode (~30 jump opcodes skip `check_for_interrupt`), and SQLite runs substantial C-level code outside the VDBE loop (tokenizer/parser, planner/codegen, B-tree/pager, external sorter, built-in SQL functions, busy-handler retry loops, and rollback cleanup) directly over raw SQL and raw DB bytes.
- **Forbidden shortcut (circular input filter):** Do **not** bridge Domain 1 to Domain 2 by adding an input premise such as "assume the SQL/DB input is well-formed," "assume compiled bytecode only loops through `check_for_interrupt`," or "assume every helper terminates quickly." That would turn a liveness proof into an input-filter tautology and fail the requirement that user input alone cannot cause liveness failure.
- **Required internal closure (two noncircular engineering paths):** The implementation gap between Domain 1 and Domain 2 must be discharged **internally inside SQLite**, via one of (or a combination of):
  1. **Internal compiler-image + bounded-helper proof (for unmodified SQLite under configured profile limits):** Prove universally over *all* raw SQL bytes and *all* raw DB bytes that:
     - *(Reachable compiler-image CFG invariant)* Every VDBE program emitted in the image of `sqlite3Prepare` / `sqlite3Reprepare` has every control-flow cycle intersecting a `check_for_interrupt` opcode (or yielding via `OP_ResultRow`) and bounded straight-line distance between checkpoints (e.g., bounded via `SQLITE_LIMIT_VDBE_OP`), **and**
     - *(Bounded-helper invariant)* Every reachable parser pass, planner pass, single-opcode helper, and cleanup routine either terminates within an explicit work bound parameterized by the profile's `SQLITE_LIMIT_*` / DB page-count bounds, or polls internally. Where unmodified 3.54.1 fails this today (Section 6), the gap stays explicitly open.
  2. **Verified internal instrumentation:** Add explicit checked polling inside SQLite itself (universal back-edge or tick-countdown polling in `sqlite3VdbeExec`, periodic polling in `sqlite3RunParser`, `sqlite3VdbeSorterRewind`, `sqlite3BtreeCount` for `xProgress`, `sqlite3InvokeBusyHandler`, and large clear/copy loops) and prove the instrumented implementation directly satisfies `PollBound K` over all raw SQL and DB bytes.

---

## 4. Fourfold Property Split: (a) Non-Termination, (b) Progress Accounting, (c) Interrupt Races, (d) Timed Budgets

| Dimension | Specification Content | `[Doc]` Guarantee | `[Abstract-VM target]` | `[Open gap]` in Real SQLite 3.54.1 `[Source-only]` |
|---|---|---|---|---|
| **(a) No unconditional termination** | Explicitly **not** claimed. Arbitrary un-cancelled SQL or raw VDBE may diverge forever. | `security.html` §1.1 acknowledges arbitrary SQL can run indefinitely. | Prove only periodic polling and cancellation-conditional return. | None (intentional non-goal). |
| **(b) Progress callback frequency (accounting units, NOT wall-clock)** | When `xProgress ≠ NULL` and `N ≥ 1`, between consecutive `xProgress` invocations while active and not returning/blocked externally, internal work is `≤ B_prog(N)` **accounting ticks** — not milliseconds. | `progress_handler.html`: `N` is the **"approximate"** number of VM instructions between calls; since 3.41.0 may also be invoked directly from `sqlite3_prepare()`. | `≤ B_prog(K, N)` internal work ticks between `pollProgress` events (and `InfinitelyOften pollProgress` under weak fairness if uncancelled & non-returning). | `nVmStep` counts 1 per VDBE op regardless of intra-op C work; `check_for_interrupt` is selective (overshoot causes catch-up `while` burst); `OP_Count` never invokes `xProgress` inside `sqlite3BtreeCount`; prepare counts 4 sparse `sqlite3ProgressCheck` calls (`nProgressSteps`), not VM ops. |
| **(c) Cooperative interrupt → return/close or clean quiescence** | If `sqlite3_interrupt(db)` is requested and visible while an operation is **strictly active** (past startup clear), the operation eventually returns (`SQLITE_INTERRUPT`, or normal completion / `SQLITE_ROW` / other error due to near-completion race). Whole-connection quiescence (`nVdbeActive = 0`) additionally requires the host to step/reset/finalize yielded statements. | `interrupt.html`: aborts pending ops "at its earliest opportunity"; cross-thread safe if `db` cannot close concurrently; near-finished op may complete normally; interrupted write in explicit txn rolls back entire txn; idle interrupt is a no-op for later statements; in effect until running statement count hits `0`. | **Finite:** `≤ K + U` internal ticks once `visible = true` in strictly-active phase. **Qualitative:** eventual `ReturnedOrYielded` under disjoint host hypotheses; `.interrupted` (or `.nomem` on OOM) if observed prior to completion/yield. | (1) Startup-clear (`L94110`, `L187596`) & `sqlite3Reprepare` clear race when `nVdbeActive == 0`; (2) `sqlite3_is_interrupted()` stays `1` after idle/finished ops until next `prepare`/`step`/`wal_checkpoint_v2`; (3) unpolled helpers & busy-handler retries; (4) non-atomic fallback if `SQLITE_ATOMIC_INTRINSICS == 0`. |
| **(d) Conditional wall-clock time budgets** | Physical-time response bound holds **only** when composing `(K, U, E_max)` with independent platform latency hypotheses `(Δ_vis, Δ_sched, τ_step, T_vfs, T_busy, T_cb, T_mutex)`. | None (no wall-clock guarantees in SQLite docs). | Algebraic corollary of finite tick bound + quantitative platform bounds. | OS scheduler preemption, disk/VFS latency, `busy_timeout` sleeps, and native instruction timing are outside SQLite's proof boundary. |

---

## 5. Noncircular Decomposition: Five Host Obligations vs Five SQLite Obligations

To ensure **"host behaves" never bakes in desired progress** (never assuming benign SQL/DB inputs or "every run hits a poll"), partition hypotheses into five independently falsifiable **Host / Environment Obligations** and five **SQLite Internal Obligations**.

### 5.1 Host / Process / Environment Obligations (Zero Reference to SQLite Inputs or Checkpoints)
1. **Scheduler Fairness (`HostWeakFairness`) / Dispatch Budget (`Δ_sched`):** If the SQLite thread is continuously enabled to take an internal step, it eventually takes a step (weak fairness). In multi-thread use, peer threads holding `db->mutex` or shared-cache B-tree mutexes eventually release them (or within `T_mutex`). `[Source-only]` `sqlite3_interrupt` does **not** acquire `db->mutex` (`L190283–L190293`), whereas `sqlite3_progress_handler`, `prepare`, `step`, `reset`, `finalize`, and `close` all do.
2. **Interrupt Delivery Visibility (`HostInterruptVisibility`) / Visibility Bound (`Δ_vis`):** Once `postInterrupt` stores `1` to `db->u1.isInterrupted`, the memory system eventually makes `1` visible to `AtomicLoad` on the executing thread (C11 relaxed-atomic forward progress / TSO store-buffer flush fairness), assuming `SQLITE_ATOMIC_INTRINSICS == 1` `[Source-only]` (`L15115–L15116`).
3. **Owner Lifetime & API Coherence (`HostLifetimeCoherent` + `HostDrivesYielded`):**
   - `db` remains live (never freed by `sqlite3_close` or final zombie cleanup in `sqlite3LeaveMutexAndCloseZombie`, `L189755` `[Source-only]`) across any concurrent `sqlite3_interrupt(db)` / `sqlite3_is_interrupted(db)` call (`[Doc]`: `interrupt.html`).
   - Callbacks (`xProgress`, `xBusy`, `xAuth`, etc.) do not violate re-entry rules by modifying the invoking connection (`[Doc]`: `progress_handler.html`).
   - For connection quiescence (`nVdbeActive = 0`), the host eventually calls `step`, `reset`, or `finalize` on any statement paused at `SQLITE_ROW`.
4. **External Call Termination / Budgets (`HostExtCallReturns` / `T_vfs, T_busy, T_cb`):**
   - Every VFS method (`xRead`, `xWrite`, `xSync`, `xLock`, `xUnlock`, `xSleep`, `xShmLock`, etc.) returns.
   - **Busy handler:** `xBusy` (including `sqliteDefaultBusyCallback` under `sqlite3_busy_timeout`, `L190102–L190144` `[Source-only]`) returns `0` after finitely many retries (or within `T_busy`). Essential because SQLite's lock-retry loops (`L62972`, `L69069`, `L76497` `[Source-only]`) **never** check `isInterrupted` or `xProgress`.
   - Every user callback returns: `xProgress`, custom SQL functions/aggregates/collations, virtual table methods (`xFilter`/`xNext`/`xColumn`/`xClose`/`xRollback`/`xDisconnect`), `xAuth`, `xTrace`/`xProfile`, `xUpdate`/`xPreUpdate`, `xCommit`/`xRollback`, `xWalCallback`, and destructors.
5. **Process Integrity:** No external memory corruption, unmasked fatal signal, or allocator hang outside SQLite (ordinary `malloc` returning `NULL` is an admitted host outcome handled via `sqlite3OomFault`, `L32653` `[Source-only]`).

### 5.2 SQLite Internal Proof Obligations (Universal ∀ Raw SQL / Raw DB Bytes / Modeled Calls)
1. **Certified Inter-Poll Work Bound (`PollBound K`):** Every pure internal work segment from an active state is bounded by `≤ K` ticks before reaching a poll, external call, yield/return, or unwind — proved via an internal rank function, never assumed on inputs.
2. **Progress-Cadence Accounting Soundness (`ProgressBound B_prog`):** With `xProgress ≠ NULL` and `N ≥ 1`, counter arithmetic cannot stall or skip polling indefinitely; work between `pollProgress` calls is `≤ B_prog(K, N)` ticks.
3. **Checkpoint Effectivity & Non-Clobber (`CancelEffectivity`):** Observing `visible = true` at a poll (or `xProgress ≠ 0`) transitions monotonically out of `active` into `unwinding`; no internal step clears `isInterrupted` while `nVdbeActive > 0`.
4. **Bounded Unwind & Cleanup (`UnwindBound U`):** From `unwinding`, cleanup completes in `≤ U` internal ticks and `≤ E_unwind` external calls, parameterized separately for read-only cleanup (`U_ro`) vs write rollback (`U_rw(dirtyPages)`).
5. **Bounded Internal Retries:** Every internal retry loop (`SQLITE_MAX_SCHEMA_RETRY = 50` `L24582`, `SQLITE_MAX_PREPARE_RETRY = 25` `L149127`, `BTCURSOR_MAX_DEPTH = 20` `L72180` `[Source-only]`) is statically bounded and preserves cancellation across retries.

---

## 6. Grounded SQLite 3.54.1 Checkpoint Placement Audit (`[Source-only]`)

A full-file scan of [`sqlite3.c`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c) (271,131 lines) enumerated **every** occurrence of `u1.isInterrupted`, `xProgress`, `nProgressOps`, `sqlite3ProgressCheck`, `checkProgress`, and `check_for_interrupt`. **All concrete native behavioral inferences in this section are `[Source-only]` unless explicitly marked `[Doc]`.**

| Phase / Routine (`sqlite3.c` link) | Polls `isInterrupted`? | Polls `xProgress`? | Accounting Unit / Cadence | Bounded Local Work Under Arbitrary SQL / Corrupt DB? `[Source-only]` | Classification |
|---|---|---|---|---|---|
| **API Control:** `sqlite3_interrupt` ([`L190283`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L190283)), `sqlite3_is_interrupted` ([`L190299`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L190299)) | Writes/reads `u1.isInterrupted` via `AtomicStore`/`AtomicLoad` ([`L15115–L15120`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L15115)). **No `db->mutex`.** | N/A | N/A | O(1) | **`[Open gap]`** Sets `isInterrupted = 1` even when `nVdbeActive == 0`; `sqlite3VdbeHalt` ([`L90980`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L90980)) never clears it, so `sqlite3_is_interrupted()` stays `1` until next `prepare`/`step`/`wal_checkpoint_v2` (contrasts with `[Doc]` "no-op when no running statements"). Non-atomic fallback if `SQLITE_ATOMIC_INTRINSICS == 0`. |
| **API Control:** `sqlite3_progress_handler` ([`L190196`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L190196)) | Acquires `db->mutex`. | Sets `xProgress`, `nProgressOps`. | `nOps > 0` else disables. | O(1) after mutex | Serialized against active `step`/`prepare` via `db->mutex`. |
| **Prepare — Parser Loop:** `sqlite3RunParser` ([`L187579`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L187579)) | Clears `isInterrupted = 0` if `nVdbeActive == 0` ([`L187596`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L187596)). Polls at [`L187644`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L187644) **only** when `tokenType >= TK_WINDOW` (whitespace, comments, window/over/filter, qnumber, illegal, EOF). | **No** | Per whitespace/special token | Bounded by `SQLITE_LIMIT_SQL_LENGTH` (default 1 GB) & parser depth, **not** per token: contiguous non-whitespace token streams skip `L187644` until end/limit and never invoke `xProgress`. | **`[Open gap]`** Startup-clear race (`L187596`) + unpolled non-whitespace token runs. |
| **Prepare — Analysis & Codegen:** `sqlite3ProgressCheck` ([`L37053`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L37053)) | **Yes** (`L37055`) | **Yes** (`L37060–L37069`, every `nProgressOps` calls) | `p->nProgressSteps` (NOT VM opcodes) | **Only 4 call sites exist:** `resizeResolveLabel` ([`L88109`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L88109), every 100 labels), `sqlite3ColumnsFromExprList` ([`L151912`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L151912)), `whereLoopOutputAdjust` ([`L172768`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L172768)), `whereLoopAddBtreeIndex` ([`L173304`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L173304), only if `nEq > 3`). Returns `void`; callers only exit on later `pParse->nErr` checks. | `[Doc]`: "might also be invoked directly from `sqlite3_prepare()`". **`[Open gap]`** Planner/codegen work between these 4 sparse sites is not uniformly bounded by `N`. |
| **Reprepare:** `sqlite3_step` ([`L94235`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L94235)) → `sqlite3Reprepare` ([`L149337`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L149337)) → `sqlite3LockAndPrepare` ([`L149287`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L149287)) | Indirectly via `sqlite3RunParser` / `sqlite3ProgressCheck`. | Indirectly via `sqlite3ProgressCheck`. | Retries capped: `SQLITE_MAX_SCHEMA_RETRY = 50` ([`L24582`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L24582)), `SQLITE_MAX_PREPARE_RETRY = 25` ([`L149127`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L149127)). | Retry counts are statically bounded, **but** when the repreparing statement was the sole active VDBE, `nVdbeActive == 0` upon entering `sqlite3RunParser` (`L187596`), which **overwrites `isInterrupted = 0`**. | **`[Open gap]`** Interrupt arriving during a schema-retry reprepare window can be silently clobbered. |
| **Execution Entry:** `sqlite3Step` ([`L94109`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L94109)) & `sqlite3VdbeExec` ([`L97214–L97235`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L97214)) | `sqlite3Step` clears `isInterrupted = 0` if `nVdbeActive == 0` (`L94110`) before `nVdbeActive++` (`L94126`). `sqlite3VdbeExec` checks `isInterrupted` at entry (`L97235`). | Sets `nProgressLimit = nProgressOps - (iPrior % nProgressOps)` (`L97218`); no callback at entry. | `nVmStep` + `iPrior` (`u32` `STMTSTATUS_VM_STEP`, wraps mod `2^32`). | Startup-clear race window between entering `sqlite3_step` and `L94110`. | **`[Open gap]`** Concurrent one-shot interrupt before `L94110` is cleared; one-shot theorem must target post-clear active phase (or persistent re-assertion). |
| **Execution — Main VDBE Loop:** `sqlite3VdbeExec` ([`L97424–L97445`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L97424)) | **Only** at `check_for_interrupt` (`L97425`), reached by: `OP_Goto` (`L97407`,`L97411`), `OP_Gosub` (`L97460`), `OP_Count` (`L100244`), `OP_Next`/`OP_Prev`/`OP_SorterNext` (`L102962`,`L102967`), `OP_IntegrityCk` (`L103752`), `OP_RowSetRead` (`L103847`,`L103853`), `OP_Program` (`L104051`), `OP_VNext` (`L105093`,`L105095`). | At `check_for_interrupt` (`L97433`) and `vdbe_return` ([`L105808`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L105808)) via `while(nVmStep >= nProgressLimit && db->xProgress != 0)`. | `nVmStep` (approximate). Overshoot triggers multi-call catch-up burst. | ~30 jump opcodes (`OP_If`, `OP_IfNot`, `OP_IfPos`, `OP_IfNotZero`, `OP_DecrJumpZero`, `OP_Yield`, `OP_Return`, `OP_Jump`, `OP_Eq`..`OP_Ge`, `OP_Once`, `OP_Rewind`, `OP_SeekRowid`, etc.) jump via `jump_to_p2` or direct `pOp = &aOp[...]` **without** polling `check_for_interrupt`. | **`[Open gap]`** Raw bytecode universal bound is **FALSE** on unmodified `sqlite3VdbeExec`. Compiler-image CFG proof (or instrumentation) is required internally (Section 3). |
| **Execution — `EXPLAIN`:** `sqlite3VdbeList` ([`L89936`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L89936)) | **Yes** (once per output row) | **No** | 1 row per `sqlite3_step` | Bounded per `sqlite3_step` call. | Polls `isInterrupted`, not `xProgress`. |
| **Execution — `OP_ResultRow` & `OP_Halt` → `vdbe_return`** ([`L97687`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L97687), [`L98112`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L98112), [`L105808`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L105808)) | `vdbe_return` does **not** check `isInterrupted` (near-completion/row-yield returns normally; next `step` catches it at `L97235`). | **Yes** (`L105808`) | Catch-up loop on `nVmStep ≥ nProgressLimit`. | **Post-commit subtlety:** `OP_Halt` runs `sqlite3VdbeHalt(p)` (which can **commit** in autocommit mode and sets `VDBE_HALT_STATE`) *before* `goto vdbe_return` (`L97696`). If `xProgress` returns non-zero at `L105810`, `abort_due_to_error` sets `p->rc = SQLITE_INTERRUPT` and returns `SQLITE_INTERRUPT` even though `sqlite3VdbeHalt` already committed (`L105781` skips halt). | **`[Open gap]`** Returning `SQLITE_INTERRUPT` from `xProgress` on final `vdbe_return` does **not** guarantee rollback occurred. |
| **Helper — `OP_Count`:** `sqlite3BtreeCount` ([`L83280`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L83280), [`L100244`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L100244)) | **Yes**, per B-tree page (`L83293`), then `check_for_interrupt` at `L100244`. | **No** inside traversal loop! Only once at `L100244` after full count. | Per page (`isInterrupted`); 1 `nVmStep` total (`xProgress`). | Depth capped at `BTCURSOR_MAX_DEPTH = 20` ([`L78219`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L78219)), so finite even on corrupt DB, but a corrupt depth-20 DAG can visit huge page-path counts without ever calling `xProgress`. | **`[Open gap]`** (`xProgress` unpolled during `sqlite3BtreeCount`; `sqlite3_interrupt` polled per page). |
| **Helper — `OP_IntegrityCk`:** `sqlite3BtreeIntegrityCheck` ([`L83367`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L83367), [`L83665`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L83665)) | **Yes**, via `checkProgress` (`L83369`). | **Yes**, via `checkProgress` (`L83375–L83385`). | `pCheck->nStep % nProgressOps == 0` (per page & error msg). | Depth capped (`L83680`, `BTCURSOR_MAX_DEPTH = 20`); polls every page in `checkTreePage` (`L83665`). | Instrumented for both, though unit is page/error visits rather than VM ops. |
| **Helper — `OP_SorterSort`:** `sqlite3VdbeSorterRewind` ([`L102775`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L102775), [`L109153`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L109153)) | **No** | **No** | 1 `nVmStep` for entire sort/merge. | Full in-memory + external merge sort runs unpolled; work scales with materialized rows, not `N`. | **`[Open gap]`** Heavy unpolled single-opcode helper. |
| **Helper — `OP_Clear` / `OP_Destroy` / Overflow / `VACUUM` Copy:** `clearDatabasePage` ([`L82979`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L82979)), `clearCellOverflow` ([`L79761`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L79761)), `accessPayload` ([`L78052`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L78052)), `sqlite3BtreeCopyFile` ([`L85135`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L85135), [`L162551`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L162551)) | **No** | **No** | 1 `nVmStep` for entire tree clear/drop/copy or overflow payload read. | Termination is finite (`BTCURSOR_MAX_DEPTH = 20` at `L82996`, decrementing `nOvfl` at `L79765`, decrementing `amt` at `L78071`), so no infinite corrupt-DB cycle, **but** work scales with full table/DB/blob size (`u32` payload / millions of pages) with zero polling. | **`[Open gap]`** Unpolled single-opcode work scaling with DB/payload size. |
| **Helper — Built-in `OP_Function` / `OP_PureFunc`** ([`L105303`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L105303)): `patternCompare` ([`L135005`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L135005)), `replaceFunc` ([`L135748`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L135748)), `printf`, JSON, FTS | **No** | **No** | 1 `nVmStep` per invocation. | Finite under `SQLITE_LIMIT_LENGTH`, `SQLITE_LIMIT_LIKE_PATTERN_LENGTH` (default 50,000, `L15045`), `SQLITE_PRINTF_PRECISION_LIMIT`; `L135003` notes worst-case `O(N^2)` for `LIKE` and recursive `*[...]` backtracking for `GLOB` (`L135038–L135042`) — finite, never infinite, but large unpolled single-op CPU work. | **`[Open gap]`** Requires tight `SQLITE_LIMIT_*` + per-builtin work bounds or internal polling. |
| **Helper — WAL Checkpoint:** `walCheckpoint` ([`L69262`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L69262)), `sqlite3_wal_checkpoint_v2` ([`L190989`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L190989)) | **Yes**, per copied WAL frame (`L69262`); clears `isInterrupted = 0` at exit if `nVdbeActive == 0` (`L190989`). | **No** | Per WAL frame copied. | `walBusyLock` ([`L69061`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L69061)) and `xSync`/truncate do **not** poll `isInterrupted`. | Polled during frame copy; unpolled during busy wait and sync. |
| **Busy / Lock Retry Loops:** `pager_wait_on_lock` ([`L62972`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L62972)), `walBusyLock` ([`L69069`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L69069)), `sqlite3BtreeBeginTrans` ([`L76497`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L76497)), `sqliteDefaultBusyCallback` ([`L190102`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L190102)) | **No** | **No** | `nBusy`; `sqliteDefaultBusyCallback` sleeps up to `db->busyTimeout` ms via `sqlite3OsSleep`. | Completely unpolled during lock contention. | **`[Open gap]` / Host Contract:** `busy_timeout` sleeps and custom `xBusy` retries ignore both `sqlite3_interrupt` and `xProgress`. |
| **OOM Interaction:** `sqlite3OomFault` ([`L32653`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L32653)), `sqlite3OomClear` ([`L32680`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L32680)) | Sets `isInterrupted = 1` if `nVdbeExec > 0`; clears `0` if `mallocFailed && nVdbeExec == 0`. | N/A | N/A | Overloads `u1.isInterrupted` for OOM abort; `SQLITE_NOMEM` overrides `SQLITE_INTERRUPT` (`L90821`, `L105756`). | Must include `.nomem` in cancellation return-code set. |
| **Cleanup / Halt / Rollback / Close:** `sqlite3VdbeHalt` ([`L90800`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L90800)), `sqlite3RollbackAll` ([`L189867`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L189867)), `sqlite3_reset` ([`L93378`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L93378)), `sqlite3_finalize` ([`L93349`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L93349)), `sqlite3Close` ([`L189638`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L189638)), `sqlite3LeaveMutexAndCloseZombie` ([`L189747`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L189747)) | **No** (atomic for DB consistency). | **No** | Scales with open cursors, dirty pages, attached DBs, vtabs. | **Read-only vs Write split ([`L90860`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L90860)):** Read-only `SQLITE_INTERRUPT` skips rollback (`!p->readOnly \|\| mrc!=SQLITE_INTERRUPT`). Write `SQLITE_INTERRUPT` ALWAYS invokes `sqlite3RollbackAll(db, SQLITE_ABORT_ROLLBACK)` ([`L90867`](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L90867)), rolling back the entire explicit txn, aborting sibling active statements with `SQLITE_ABORT_ROLLBACK`, and running journal VFS I/O, vtab `xRollback`, and `xRollbackCallback`. Zombie close also rolls back and may checkpoint WAL unless `SQLITE_DBCONFIG_NO_CKPT_ON_CLOSE`. | **`[Abstract-VM target]` / Non-Claim:** Keep `U_ro` separate from `U_rw(dirtyPages)` + VFS/rollback-callback budgets; rollback is intentionally non-interruptible. |

### Semantic Distinction: `xProgress ≠ 0` vs `sqlite3_interrupt()` (`[Source-only]`)
Do **not** collapse these two mechanisms into one boolean:
- **`sqlite3_interrupt(db)`** sets the **connection-wide** `db->u1.isInterrupted = 1` (lock-free, no `db->mutex`), affecting all active statements on `db` until `nVdbeActive == 0`, observable via `sqlite3_is_interrupted(db)`, and checked in `sqlite3BtreeCount`, `walCheckpoint`, `sqlite3RunParser`, `sqlite3VdbeList`, and `sqlite3VdbeExec` entry where `xProgress` is not.
- **`xProgress(pArg) ≠ 0`** aborts **only the invoking statement or parse** (`L37066`, `L83381`, `L97438`, `L105812`) and does **not** set `db->u1.isInterrupted = 1`. Sibling read-only statements continue unaffected and `sqlite3_is_interrupted(db)` remains `0` — except when the aborted statement is a writer, in which case `sqlite3VdbeHalt` calls `sqlite3RollbackAll(db, SQLITE_ABORT_ROLLBACK)` (`L90867`), aborting sibling statements with `SQLITE_ABORT_ROLLBACK`.

---

## 7. Abstract VM Trace Sketches, Lean Theorem Sketches (`UNCOMPILED`), and Negative Model Witness

> **WARNING — UNCOMPILED DESIGN SKETCH:** All Lean 4 code and traces below describe the **Domain 1 abstract checked VM** (`[Abstract-VM target]`). Nothing below has been compiled with `lake build`, and nothing below is a native SQLite reproduction program.

### 7.1 Canonical Abstract Execution Trace Sketches

1. **Strictly-active cooperative cancellation (`≤ K + U` work ticks after visibility):**
   ```text
   t=0: active(vm₀, rem=k) [nActive=1, posted=F, visible=F]
     --(postInterrupt)-->      active(vm₀, rem=k) [posted=T, visible=F]
     --(deliverInterrupt)-->   active(vm₀, rem=k) [posted=T, visible=T]
     --(work × ≤k)-->          active(vm_k, rem=0) [visible=T]
     --(pollInterrupt true)--> unwinding(u ≤ U, .interrupted)
     --(work × u)-->           unwinding(0, .interrupted)
     --(returnOp .interrupted)--> returned(.interrupted) [nActive=0]
   ```
2. **Near-completion race (explicitly allowed by `[Doc]` `interrupt.html`):**
   ```text
   t=0: active(vm_final, rem=1) [nActive=1, posted=T, visible=F]
     --(work)-->               unwinding(0, .done)   -- or directly returnOp(.row cells)
     --(deliverInterrupt)-->   unwinding(0, .done) [visible=T]
     --(returnOp .done)-->     returned(.done)       -- valid: op finished before next poll
   ```
3. **Startup-clear / `sqlite3Reprepare` clobber race (`[Source-only]` `L94110`, `L187596`):**
   ```text
   t=0: starting [nActive=0, posted=F, visible=F]
     --(postInterrupt)-->      starting [nActive=0, posted=T, visible=F]
     --(deliverInterrupt)-->   starting [nActive=0, posted=T, visible=T]
     --(startupClear)-->       active(vm₀, rem=K) [nActive=1, posted=F, visible=F]  -- clobbered!
   ```
   *Modeling consequence:* A one-shot interrupt theorem **must** require `StrictlyActive` (past `startupClear`, `nActive > 0`) as its precondition; covering `starting` / reprepare requires either a persistent re-asserting interrupt host or eliminating the `nVdbeActive == 0` clear race internally.
4. **Negative-witness trace (fair host, missing internal checkpoint):**
   ```text
   t=0: active(vm_loop) [nActive=1]
     --(postInterrupt)-->      active(vm_loop) [posted=T, visible=F]
     --(deliverInterrupt)-->   active(vm_loop) [posted=T, visible=T]
     --(work)-->               active(vm_loop) [visible=T]
     --(work)-->               active(vm_loop) [visible=T]  -- loops forever; 0 stutter, 0 ext calls!
   ```

### 7.2 Minimal Lean-Shaped Definitions & Theorem Suite (**UNCOMPILED**)

```lean
-- UNCOMPILED DESIGN SKETCH (not typechecked; no repository code modified)

namespace Silmaril.Machine.SQLite.VirtualMachine.Responsiveness

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SQLite.VirtualMachine.Isolation

/-- External call classes whose termination/latency is a host obligation. -/
inductive ExtKind where
  | vfs | busy | udf | vtab | progressCb | rollbackHook | mutexAcquire
  deriving DecidableEq

/-- Operation return codes. Near-completion permits `done`, `row`, or `fault`
even after `postInterrupt`; concurrent OOM permits `nomem`. -/
inductive ReturnCode where
  | done | row (cells : List Value) | interrupted | nomem | busy | fault (reason : ProfileFault)
  deriving DecidableEq

/-- Explicit lifecycle phases separating pre-clear `starting`, strictly-active
execution (`workRem ≤ K`), external calls, non-interruptible `unwinding` (`rem ≤ U`),
paused `SQLITE_ROW` (`yielded`), completion, and `closed`. -/
inductive OpPhase where
  | idle
  | starting
  | active (vm : State) (workRem : Nat)
  | inExt (kind : ExtKind) (resume : State)
  | unwinding (rem : Nat) (rc : ReturnCode)
  | yielded (cells : List Value) (vm : State)
  | returned (rc : ReturnCode)
  | closed

/-- Separates cross-thread request (`posted`) from memory visibility (`visible`). -/
structure InterruptState where
  posted : Bool := false
  visible : Bool := false
  deriving DecidableEq

/-- Progress callback configuration (`period ≥ 1` when enabled). -/
structure ProgressCfg where
  enabled : Bool := false
  period : Nat := 0
  period_pos : enabled = true → 0 < period
  ticksUntilProgress : Nat := 0

structure Config where
  host : HostState
  phase : OpPhase
  intr : InterruptState
  prog : ProgressCfg
  nActive : Nat             -- models `db->nVdbeActive`
  isWriteTxn : Bool         -- separates read-only cleanup (`U_ro`) from write rollback (`U_rw`)

inductive Act where
  | work
  | pollInterrupt (seen : Bool)
  | pollProgress (cancel : Bool)
  | extCall (kind : ExtKind)
  | extRet (kind : ExtKind)
  | startupClear
  | postInterrupt
  | deliverInterrupt
  | hostDrive
  | returnOp (rc : ReturnCode)
  | stutter
  deriving DecidableEq
```

In the checked abstract VM transition relation `LiveStep (profile : Profile) (K U : Nat) (raw : Vdbe.RawProgram) : Config → Act → Config → Prop` (with `FallbackLive` for unmodeled opcodes, universal over all `raw`):
- Every `Act.work` in `active vm r` strictly decreases `r` (`r = 0` forces a poll, `extCall`, `unwinding`, or `returnOp`).
- `pollInterrupt true` in `active` enters `unwinding u .interrupted` (`u ≤ U`); `pollProgress true` enters `unwinding u .interrupted` **without** setting `intr.visible := true`.
- No internal step clears `intr.visible` while `nActive > 0`.
- Every `Act.work` in `unwinding (r + 1) rc` strictly decreases `r`; `unwinding 0 rc` emits `returnOp rc`.

```lean
-- UNCOMPILED DESIGN SKETCH

structure IRun (profile : Profile) (K U : Nat) (raw : Vdbe.RawProgram) where
  st : Nat → Config
  act : Nat → Act
  step : ∀ t, LiveStep profile K U raw (st t) (act t) (st (t + 1))

def StrictlyActive (cfg : Config) : Prop :=
  ∃ vm r, cfg.phase = .active vm r ∧ 0 < cfg.nActive

def ReturnedOrYielded (cfg : Config) : Prop :=
  (∃ rc, cfg.phase = .returned rc) ∨ (∃ row vm, cfg.phase = .yielded row vm)

/-- **Theorem 1 (Certified Inter-Poll Work Bound — finite, no fairness needed):**
Universal over ALL `raw : Vdbe.RawProgram`, ALL `host`, ALL `profile`. -/
theorem inter_poll_work_bound
    (profile : Profile) (K U : Nat) (raw : Vdbe.RawProgram)
    (ρ : IRun profile K U raw) (t : Nat)
    (hact : StrictlyActive (ρ.st t)) :
    ∃ d ≤ K, ρ.act (t + d) ≠ .work

/-- **Theorem 2 (Progress Callback Frequency in Accounting Units — NOT wall-clock):**
With `xProgress` enabled at period `N ≥ 1`, at most `B_prog K N` internal `Act.work`
ticks occur before `pollProgress`, `extCall`, `unwinding`, or `ReturnedOrYielded`.
Does NOT claim query termination if `xProgress` continues returning `false`. -/
theorem progress_poll_work_bound
    (profile : Profile) (K U : Nat) (raw : Vdbe.RawProgram)
    (ρ : IRun profile K U raw) (t : Nat)
    (hact : StrictlyActive (ρ.st t))
    (hen : (ρ.st t).prog.enabled = true) :
    ∃ w ≤ B_prog K (ρ.st t).prog.period,
      ReachesBeforeWorkLimit ρ t w
        (fun i => (∃ c, ρ.act i = .pollProgress c) ∨
                  (∃ k, ρ.act i = .extCall k) ∨
                  ReturnedOrYielded (ρ.st i) ∨
                  (∃ u rc, (ρ.st i).phase = .unwinding u rc))

/-- **Theorem 3 (Finite Tick-Bounded Cancellation — NO fairness needed):**
Once `intr.visible = true` in a strictly-active state, at most `K + U` internal
`Act.work` ticks occur before `ReturnedOrYielded`. -/
theorem cancel_within_work_bound
    (profile : Profile) (K U : Nat) (raw : Vdbe.RawProgram)
    (ρ : IRun profile K U raw) (t : Nat)
    (hact : StrictlyActive (ρ.st t))
    (hvis : (ρ.st t).intr.visible = true) :
    WorkTicksUntil ρ t (fun i => ReturnedOrYielded (ρ.st i)) ≤ K + U

-- Five disjoint, noncircular host hypotheses (none mention SQLite inputs or checkpoints):
def HostWeakFairness (ρ : IRun profile K U raw) : Prop :=
  ∀ t, (∀ t' ≥ t, InternalStepEnabled (ρ.st t')) → ∃ t' ≥ t, IsInternalAct (ρ.act t')

def HostInterruptVisibility (ρ : IRun profile K U raw) : Prop :=
  ∀ t, StrictlyActive (ρ.st t) → (ρ.st t).intr.posted = true →
       ∃ t' ≥ t, ReturnedOrYielded (ρ.st t') ∨ (ρ.st t').intr.visible = true

def HostExtCallReturns (ρ : IRun profile K U raw) : Prop :=
  ∀ t k, ρ.act t = .extCall k → ∃ t' > t, ρ.act t' = .extRet k

def HostLifetimeCoherent (ρ : IRun profile K U raw) : Prop :=
  ∀ t, ρ.act t = .postInterrupt → (ρ.st t).phase ≠ .closed

def HostDrivesYielded (ρ : IRun profile K U raw) : Prop :=
  ∀ t row vm, (ρ.st t).phase = .yielded row vm → ∃ t' ≥ t, ρ.act t' = .hostDrive

/-- **Theorem 4 (Qualitative Cooperative Cancellation — Fairness Bridge):**
Universal over ALL `raw : Vdbe.RawProgram`, ALL `host`, ALL `profile`. -/
theorem cancel_liveness_of_fairness
    (profile : Profile) (K U : Nat) (raw : Vdbe.RawProgram)
    (ρ : IRun profile K U raw)
    (hfair : HostWeakFairness ρ) (hvis : HostInterruptVisibility ρ)
    (hext : HostExtCallReturns ρ) (hlife : HostLifetimeCoherent ρ)
    (t : Nat) (hact : StrictlyActive (ρ.st t)) (hpost : ρ.act t = .postInterrupt) :
    ∃ t' ≥ t, ReturnedOrYielded (ρ.st t')

/-- **Corollary 4b (Connection Quiescence):** Adding `HostDrivesYielded` yields
eventual `nActive = 0`. -/
theorem quiescence_of_fairness
    (profile : Profile) (K U : Nat) (raw : Vdbe.RawProgram)
    (ρ : IRun profile K U raw)
    (hfair : HostWeakFairness ρ) (hvis : HostInterruptVisibility ρ)
    (hext : HostExtCallReturns ρ) (hlife : HostLifetimeCoherent ρ)
    (hdrive : HostDrivesYielded ρ)
    (t : Nat) (hact : StrictlyActive (ρ.st t)) (hpost : ρ.act t = .postInterrupt) :
    ∃ t' ≥ t, (ρ.st t').nActive = 0

/-- **Corollary 5 (Conditional Wall-Clock Budget — ONLY with independent timing bounds):**
Explicitly conditional on `(Δ_vis, Δ_sched, τ_step, T_ext)`; NOT an intrinsic SQLite SLA. -/
theorem conditional_wall_clock_bound
    (profile : Profile) (K U E_max : Nat) (raw : Vdbe.RawProgram)
    (ρ : IRun profile K U raw) (time : Nat → Nat)
    (Δ_vis Δ_sched τ_step T_ext : Nat)
    (hTimedVis   : TimedInterruptVisibility ρ time Δ_vis)
    (hTimedSched : TimedSchedulerDispatch ρ time Δ_sched τ_step)
    (hTimedExt   : TimedExternalBudget ρ time E_max T_ext)
    (t : Nat) (hact : StrictlyActive (ρ.st t)) (hpost : ρ.act t = .postInterrupt) :
    ∃ t' ≥ t, ReturnedOrYielded (ρ.st t') ∧
      time t' - time t ≤ Δ_vis + (K + U + 1) * (Δ_sched + τ_step) + E_max * T_ext
```

### 7.3 Negative Model Witness Separating Fair Scheduling from Unbounded Internal Work (**UNCOMPILED**)

To prove our host hypotheses are **noncircular** (they do not silently imply progress without SQLite's internal `PollBound K`), define an abstract counterexample transition system `UnpolledBackEdgeVM` containing one purely symbolic abstract instruction `AbstractOp.unpolledSelfLoop` that transitions via `Act.work` back to itself without polling `intr.visible` or `prog` (this is an abstract-model witness, **not** a native SQLite reproducer):

```lean
-- UNCOMPILED DESIGN SKETCH (abstract model witness only; not a SQLite payload)

theorem negative_witness_fair_host_still_hangs
    (profile : Profile) (host : HostState) :
    ∃ (ρ : UnpolledIRun profile abstractUnpolledLoop),
      StrictlyActive (ρ.st 0) ∧
      ρ.act 1 = .postInterrupt ∧
      (ρ.st 2).intr.visible = true ∧
      HostWeakFairness ρ ∧            -- maximally fair: takes `Act.work` at every t ≥ 3
      HostInterruptVisibility ρ ∧     -- immediate 1-step visibility
      HostExtCallReturns ρ ∧          -- vacuous: zero external calls
      HostLifetimeCoherent ρ ∧        -- connection stays open forever
      (∀ t, ¬ ReturnedOrYielded (ρ.st t)) ∧
      (∀ t c, ρ.act t ≠ .pollProgress c)
```

**What this witness establishes:**
1. The conjunction of all host hypotheses (`HostWeakFairness ∧ HostInterruptVisibility ∧ HostExtCallReturns ∧ HostLifetimeCoherent`) does **not** entail responsiveness on its own.
2. SQLite's internal `PollBound K` + `CancelEffectivity` + `UnwindBound U` obligations are strictly necessary and non-redundant.

---

## 8. Layered Refinement Roadmap to Native SQLite 3.54.1

| Layer | Target & Scope | Required Obligations | Current Status |
|---|---|---|---|
| **Layer 1 — Abstract Checked VM** | `VirtualMachine.Responsiveness` over arbitrary `Vdbe.RawProgram` and `HostState`, sibling to `Isolation`. | Prove Theorems 1–5 + compiled `negative_witness_fair_host_still_hangs`. Parameterize over cleanup/rollback interface so a writable-VM extension plugs in cleanly. | **`[Abstract-VM target]`** (Jan milestone) |
| **Layer 2 — Real SQLite 3.54.1 C/VDBE Correspondence** | Arbitrary raw SQL + raw DB bytes under a `security.html`-hardened profile (`DEFENSIVE=1`, `TRUSTED_SCHEMA=0`, strict `sqlite3_limit(...)`, `mmap_size=0`, bounded/disabled `busy_timeout`). | Close Domain 1 → Domain 2 **internally** (never via an input filter): either (a) prove compiler-image CFG polling + bounded single-opcode helpers for the configured profile, or (b) add and verify internal polling checkpoints in `sqlite3VdbeExec`, `sqlite3RunParser`, `sqlite3VdbeSorterRewind`, `sqlite3BtreeCount` (`xProgress`), `sqlite3InvokeBusyHandler`, and clear/copy helpers; model startup/`sqlite3Reprepare` clear race and `U_rw(dirtyPages)` rollback explicitly. | **`[Open gap]`** (Follow-on) |
| **Layer 3 — Memory-Model & Mutex Bridge** | `AtomicStore`/`AtomicLoad` (`__ATOMIC_RELAXED` `L15115–L15116` `[Source-only]`) + `db->mutex` contention. | Refine `postInterrupt`/`deliverInterrupt` under x86-TSO FIFO store-buffer flush fairness (extending [confined lock release](sqlite-confined-release.md)); verify `SQLITE_ATOMIC_INTRINSICS == 1` in target build. | **`[Open gap]`** (Follow-on) |
| **Layer 4 — Native ELF (`libsqlite3.so`)** | Compiled x86-64 shared library. | End-to-end binary refinement of interrupt/progress/unwind paths. | **`[Open gap]`** (Long-term; no native claim until discharged) |

---

## 9. Recommendations: Jan Milestone vs Follow-On

- **January milestone (~350–500 LOC Lean):**
  1. Implement and compile `Silmaril.Machine.SQLite.VirtualMachine.Responsiveness.{Defs,Thms,Checks}` (Theorems 1–4, Corollaries 4b & 5, plus compiled `negative_witness_fair_host_still_hangs`), keeping `VirtualMachine.Isolation` untouched and parameterizing rollback unwind cleanly for follow-on writable-VM composition.
  2. Maintain the Section 6 **3.54.1 Checkpoint & Gap Ledger** alongside project docs with explicit `[Doc]` / `[Source-only]` / `[Abstract-VM target]` / `[Open gap]` discipline and zero native overclaims.
- **Follow-on (post-Jan):**
  1. Instantiate `UnwindBound U_rw(dirtyPages)` on top of a writable-VM transaction/rollback model, capturing `sqlite3VdbeHalt` / `sqlite3RollbackAll` and sibling `SQLITE_ABORT_ROLLBACK` propagation (separate from `xProgress ≠ 0`).
  2. Execute Layer-2 internal closure: mechanically audit SQLite 3.54.1 bytecode generation for unpolled cycles and evaluate either a tightly profiled helper-bounded subset or verified internal polling patches (plus addressing the `OP_Halt`→`vdbe_return` post-commit `xProgress` ordering).
  3. Build the Layer-3 TSO store-buffer flush fairness bridge for `u1.isInterrupted` and multi-statement `nVdbeActive` / reprepare race modeling.
