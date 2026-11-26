# SQLite Read-Only Isolation Proof Plan: Universal `$BAD_THING` Exclusion via ITree Effects, Prepared VM Safety, and Path to Native ELF

**Status:** Initial abstraction design (staff technical design doc; no PR or repo edits).  
**Target:** January Autoresearch target — Linux x86-64 ELF `libsqlite3.so` (pinned SQLite 3.54.1, `corpus/elf/sqlite/x86_64/libsqlite3.so`, SHA-256 `fcdd0cd75ea98cee14f2743832c6ad2ed4dd4229e2b5093f8bce7dc33c9c17f8`) and two ELF clients: the batch shell (`corpus/elf/sqlite/x86_64/sqlite3`, SHA-256 `26c71865aa7f7ce686f47e8b3c306b98b3d7fb3b181a759f388bb01284c1b870`) and an independent C client dynamically linked against `libsqlite3.so`.  
**Coordinate with:** Two sibling tasks implementing the first ITree and VM proofs; this design accommodates them without requiring current imports or build dependencies on them.

---

## 1. Organizing Claim, Threat Profile, and Explicit Non-Claims

### Organizing Claim: Universal `$BAD_THING` Exclusion
The core theorem target is **not** an input-validation or accept/reject gate. It is a **universal safety guarantee over arbitrary inputs**:

> **For ANY input** (arbitrary SQL byte strings, arbitrary bound parameters, arbitrary database file bytes, and arbitrary host/VFS replies subject to the stated host contract) **and a configured read-only profile `prof`**, **every finite execution prefix** across connection open, parsing, preparation, VM execution, and cleanup **never exhibits `$BAD_THING`**.

Concretely:
- **No input-filter premises:** Top-level theorems carry **no** assumption that the SQL input is well-formed, in a selected SQL subset, admitted by a front-end filter, within a size/depth limit, or early-rejected, and **no** assumption that database bytes are valid SQLite pages.
- **Profile is separate from input:** The profile `prof` configures the deployment boundary (protected DB path, read-only API/host policy, internal execution mechanisms/limits). Internal limits (e.g., parser depth, register/cursor bounds, read-only flags, authorizer checks) are *mechanisms inside execution*, not preconditions on the input.
- **Outcome-orthogonal:** Whether an execution returns a normal result, returns a SQLite error code, returns another valid outcome, or silently diverges is **orthogonal** to prefix safety. There is **no requirement to force refusal** on any input; the guarantee is solely that `$BAD_THING` never occurs on any finite prefix.
- **No query-result correctness needed:** We do not prove that returned rows match relational SQL semantics. Parsing/preparation need only avoid `$BAD_THING` itself and—whenever it produces a VM program—establish the internal invariants that ensure subsequent VM execution and cleanup also avoid `$BAD_THING`.

### Concrete `$BAD_THING` Catalog (Read-Only Single-Connection Profile)
Under a configured `ReadOnlyApiProfile`, `$BAD_THING` is split into **separately named properties** so program behavior, host commitment, external actors, and native memory safety are never conflated:
1. **Attempted forbidden requests (`NoAttemptedBadReq`):** The program never *attempts* a forbidden request `BadEvent prof q` on any finite prefix (even a pending `.request` that receives no handler reply): writing or truncating a file, opening the DB read-write or opening an out-of-profile path, `ATTACH`/`DETACH`, dynamic extension loading (`sqlite3_load_extension` / `dlopen`), or unmodeled temp-file/OS operations.
2. **Committed host effects (`NoCommittedBadEffect` / `NoProtectedFsMutation`):** No completed handler transition (`step q s r s'`) commits a forbidden host effect or mutates the protected host state (`fsView s' ≠ fsView s`).
3. **Protected-state nonmutation vs. external actor effects:** `NoProtectedFsMutation` guarantees only that *this* single-connection SQLite execution does not mutate the protected filesystem view under `HostContract`. It does **not** rule out concurrent external actors (other OS processes, kernel/admin actions, or shared-storage writers) modifying the underlying files outside the modeled handler.
4. **Abstract memory invariants vs. native memory safety:** In the high-level VM, `VmInv` enforces **abstract structural invariants** (bounds on `pc`, `regs`, `cursors`, read-only cursor mode, and handle ownership). This is strictly weaker than **native x86-64 memory safety** (absence of out-of-bounds loads/stores, use-after-free, stack/heap corruption, or control-flow hijack in `libsqlite3.so`), which remains an explicit Layer 5 native obligation.

### Threat Profile
- **Execution model:** Single connection, single thread (sequential).
- **Attacker-controlled inputs:** Arbitrary SQL `ByteArray` and arbitrary DB file bytes (including truncated, corrupt, or adversarial bytes, and arbitrary VFS short reads or I/O errors).
- **Permitted effects:** Opening the designated protected database read-only, reading DB pages/metadata, emitting query result rows/diagnostics, and closing handles cleanly.
- **Non-vacuity:** Concrete legitimate read-only queries (point and scan `SELECT`s) are witnessed to actually read the DB and return rows without triggering `$BAD_THING`.

### Explicit Non-Claims
This abstraction and its initial proofs do **not** claim:
1. **Confidentiality / noninterference** (data leakage from the permitted read-only DB or timing/side channels).
2. **Termination / liveness** (arbitrary inputs or cyclic/corrupt B-tree bytes may diverge; safety holds over every finite prefix).
3. **Blanket resource caps** (CPU/memory/time bounds beyond explicit internal mechanisms).
4. **Security of real upstream SQLite** (this is an initial abstract model, not a verification of `libsqlite3.so`).
5. **C/ELF refinement or native memory safety from high-level theorems** (high-level VM/ITree invariants `VmInv` are abstract structural invariants; they do not imply x86-64 memory safety or `libsqlite3.so` confinement until Layers 5–8 are discharged).
6. **Protection against external actors** (single-connection nonmutation does not prevent external OS processes from mutating files outside the modeled handler).
7. **Exploit development or reproduction** (out of scope; no real attack payloads are used in any scenario).

### Silmaril Engineering & Trust Conventions
- **Axioms:** Standard Lean axioms only (`propext`, `Classical.choice`, `Quot.sound`) per `policy.toml`; no `sorry`, no `native_decide`, no custom axioms; CI builds with `--wfail`.
- **Module & Region discipline:** Use `module` / `public import`, keep headers (`Defs.lean`, `Thms.lean`) readable with long proofs in `Silmaril/Proofs/...`, and respect `regions.toml` (`Semantics` → `Machine` → `Process` → `Elf` / `Containers`). Any inherited assumptions in native corpus models (e.g., `Entry` in `Silmaril.Elf.Corpus.SqliteRead`) remain explicit hypotheses.

---

## 2. ITree Event Model, Profile vs. `$BAD_THING`, and Host Nonmutation

### Existing Silmaril ITree APIs (Verified in Repo)
Silmaril already provides two interoperable ITree layers; new isolation modules should target `Silmaril.Elgot.ITree` directly and bridge to `TrackA.Interaction` where coalgebraic handlers are used:
1. **Weak coherent-approximation ITrees** (`Silmaril.Semantics.ITree.Defs`, namespace `Silmaril.Elgot.ITree`):
   - `Tree E A`, `Visible E A X` (`.ret`, `.vis`), `ret`, `vis`, `tau` (definitional identity), `diverge`, `bind`, `iter`.
   - Finite observations (`Silmaril.Semantics.ITree.Trace.Defs`): `Trace E A` (`.prefix`, `.request e`, `.exchange e r tail`, `.result a`), `HasTrace t p`, `TraceLE`.
   - Stateful relational handlers (`Silmaril.Semantics.ITree.Reindex.Defs`, `Trace/Handled/Defs.lean`): `Handler S E := (q : Request E) → S → q.1 → S → Prop`, `Replay step s p`, `HandledTrace step s t p`, `ReturnsTo`.
   - Syntactic prefix safety (`Silmaril.Process.ITreeTrace.Defs`): `Trace.Allows`, `Allows prog permitted` (checks every attempted request in every finite trace, including pending requests), plus `Sequential` / `Flatten` over `TypedSyscall.Kernel`.
   - Exact single-exchange lowering (`Silmaril.Semantics.ExactITree.Defs`): `Signature`, `Signature.Hom`, `Profile`, `Completion`, `Kernel`, `Config`.
2. **Coalgebraic delayed ITrees** (`Silmaril.Semantics.TrackA.Interaction.Defs`, namespace `Silmaril.Semantics.TrackA.Interaction`):
   - `Signature` (`Request`, `Response`), `Node` (`.ret`, `.tau`, `.vis`, `.branch`), `Coalgebra`, `ITree`, total `Coalgebra.Handler`, `Coalgebra.Follows`, `WeakITree.toDelayed` (`WeakITree/Defs.lean`).
   - Already instantiated for SQLite VFS/Pager in `Silmaril.Machine.SQLite.TrackA.Read.Interaction` (`VfsSignature`, `vfsTree`, `pagerHandler`, `pagerTree`).

### Lean-Shaped Event Signature, Profile, and `$BAD_THING` (Pseudocode)
*Note: Identifiers prefixed with `Silmaril.Elgot.ITree.*` or `Silmaril.Machine.SqliteVfs.*` are real repo APIs; the `SqliteIso` definitions below are design pseudocode.*

```lean
-- PSEUDOCODE (target namespace: e.g. Silmaril.Machine.SQLite.Isolation)
open Silmaril.Elgot.ITree
open Silmaril.Machine.SqliteVfs (Handle Mode Bytes ReadReply)

/-- DB-read requests vs host/privileged effect requests. -/
inductive DbReadReq where
  | openDb (path : String) (mode : Mode)
  | readPage (h : Handle) (offset count : Int)
  | fileSize (h : Handle)
  | closeDb (h : Handle)

inductive HostEffectReq where
  | emitRow (cells : List SqlVal)
  | writeFile (h : Handle) (offset : Int) (data : Bytes)
  | truncateFile (h : Handle) (size : Int)
  | attachDb (path : String)
  | loadExtension (path : String)
  | tempFileOp (op : String)

/-- Indexed ITree event family `E : Type → Type` for `Silmaril.Elgot.ITree.Tree`. -/
inductive IsoEvent : Type → Type where
  | dbRead (req : DbReadReq) : IsoEvent (DbReadResp req)
  | host   (req : HostEffectReq) : IsoEvent (HostEffectResp req)

/-- Arbitrary terminal outcome (success, error code, or bounded fault).
    Silent divergence is `ITree.diverge` (no `ret`); finite internal steps are `tau`.
    Prefix safety is completely orthogonal to which outcome (or divergence) occurs. -/
inductive IsoOutcome where
  | done (rowsEmitted : Nat)
  | err  (code : SqliteErr)
  | fault (reason : VmFault)

abbrev IsoProg := Tree IsoEvent IsoOutcome

/-- Deployment profile, kept strictly separate from untrusted inputs. -/
structure ReadOnlyApiProfile where
  protectedPath : String
  allowRowEmit  : Bool := true

/-- Explicit `$BAD_THING` predicate on attempted requests under `prof`. -/
def BadEvent (prof : ReadOnlyApiProfile) : Request IsoEvent → Prop
  | ⟨_, .dbRead (.openDb p .readOnly)⟩  => p ≠ prof.protectedPath
  | ⟨_, .dbRead (.openDb _ .readWrite)⟩ => True
  | ⟨_, .dbRead (.readPage _ _ _)⟩      => False
  | ⟨_, .dbRead (.fileSize _)⟩          => False
  | ⟨_, .dbRead (.closeDb _)⟩           => False
  | ⟨_, .host (.emitRow _)⟩             => prof.allowRowEmit = false
  | ⟨_, .host (.writeFile ..)⟩          => True
  | ⟨_, .host (.truncateFile ..)⟩       => True
  | ⟨_, .host (.attachDb _)⟩            => True
  | ⟨_, .host (.loadExtension _)⟩       => True
  | ⟨_, .host (.tempFileOp _)⟩          => True

/-- Property A (Program-side): Every request ATTEMPTED in finite trace `p`
    (including a pending `.request` with no reply) avoids `BadEvent prof`. -/
def NoAttemptedBadReq (prof : ReadOnlyApiProfile) : Trace IsoEvent IsoOutcome → Prop
  | .prefix | .result _ => True
  | .request e => ¬ BadEvent prof ⟨_, e⟩
  | .exchange e _ tail => ¬ BadEvent prof ⟨_, e⟩ ∧ NoAttemptedBadReq prof tail

/-- Property B (Host-side): No COMPLETED exchange in `p` commits a forbidden
    host transition or mutates the protected state `fsView` along the handled run. -/
def NoCommittedBadEffect (prof : ReadOnlyApiProfile) {S : Type}
    (step : Handler S IsoEvent) (fsView : S → HostFsView)
    (s0 : S) (p : Trace IsoEvent IsoOutcome) : Prop :=
  ∀ sEnd, ReachesState step s0 p sEnd → fsView sEnd = fsView s0

/-- Host/handler contract: any transition committed by this connection on a non-bad
    request preserves `fsView`. Replies to `readPage` may still be arbitrary bytes,
    short reads, or I/O errors. External actors outside `step` are out of scope. -/
structure HostContract (prof : ReadOnlyApiProfile) {S : Type}
    (step : Handler S IsoEvent) (fsView : S → HostFsView) : Prop where
  preservesFs :
    ∀ {q : Request IsoEvent} {s s' : S} {r : q.1},
      ¬ BadEvent prof q → step q s r s' → fsView s' = fsView s
```

### Attempted Forbidden Requests vs. Committed Host Effects (and External Actors)
- **`NoAttemptedBadReq` vs. `NoCommittedBadEffect`:** `NoAttemptedBadReq prof p` (equivalently `Trace.Allows (fun q => ¬ BadEvent prof q)`) is a **program-side** property: the program never *attempts* a forbidden request across any typed handler replies. **It does not by itself imply `NoCommittedBadEffect` (`fsView sEnd = fsView s0`).** Committed host nonmutation holds **only** when `NoAttemptedBadReq` is composed with `HostContract`. Conversely, a read-only handler (`Silmaril.Machine.SqliteVfs.ReadOnlyLaw`) can satisfy `NoCommittedBadEffect` even if a write is *attempted* (by returning `.error .readOnly`, proved in `readOnly_trace_bytes` and `PageRead.RejectedMutation.retains_with_rejections`). Proving **both** gives defense in depth: the engine never attempts `BadEvent`, *and* the VFS/OS layer never commits a protected-state mutation.
- **Protected-state nonmutation vs. external actor effects:** `NoCommittedBadEffect` / `HostContract` scopes nonmutation strictly to transitions `step` issued by this single connection. If an external OS process modifies the database file concurrently, that external effect is outside `step` (though arbitrary/changing read replies are already tolerated by universal quantification over `readPage` replies).

### Finite Prefix Safety vs. Liveness
- **Finite prefix safety (the organizing claim):** Quantifies over every finite `Trace IsoEvent IsoOutcome` in `HasTrace` / `HandledTrace`, including `.prefix` and pending `.request e`. Silent divergence (`diverge`) contributes only `.prefix`, so non-terminating runs satisfy prefix safety whenever all reachable finite prefixes avoid `$BAD_THING`.
- **Liveness / termination (orthogonal, out of scope):** Proved only on small concrete witnesses (§5) to show the model is non-degenerate.

---

## 3. Prepared High-Level VM Grammar, Internal Invariants, and All-Stage Coverage

The existing `Silmaril.Formats.Sqlite.Vdbe` and `Silmaril.Machine.SQLite.VirtualMachine` model a read-only VDBE core (`init`, `goto`, `halt`, `integer`, `int64`, `string8`, `null`, `copy`, `openRead`, `rewind`, `next`, `column`, `rowid`, `resultRow`, `seekRowid`) over an in-memory `Database` snapshot, plus `Traced` (`Event.openRead`, `Event.row`) and `Mutable` (`String8` self-rewrite). To model full single-connection execution on arbitrary inputs, the isolation VM tracks prepared state, cursor ownership, callbacks/subprograms, and cleanup:

```lean
-- PSEUDOCODE (representative prepared VM grammar & state)
inductive CallbackId | builtinCollation (id : Nat) | builtinPureScalar (id : Nat)
inductive SubprogId  | none -- read-only profile permits no trigger/write subprograms

inductive VmInstr where
  | init (target : Nat) | goto (target : Nat) | halt (code : Nat)
  | loadConst (dst : Nat) (val : SqlVal) | copy (src dst : Nat)
  | openRead (cur : Nat) (root dbIdx : Nat) | closeCursor (cur : Nat)
  | rewind (cur emptyTarget : Nat) | next (cur loopTarget : Nat)
  | seekRowid (cur missTarget keyReg : Nat)
  | column (cur col dst : Nat) | rowid (cur dst : Nat)
  | resultRow (first count : Nat)
  | callBuiltin (cb : CallbackId) (argFirst argc dst : Nat)
  | callSubprog (sp : SubprogId)       -- excluded by internal ReadOnly policy
  | openWrite (cur root dbIdx : Nat)   -- excluded by internal ReadOnly policy

structure PreparedProg where
  code       : Array VmInstr
  nRegs      : Nat
  nCursors   : Nat
  allowedCbs : CallbackId → Prop       -- pure, non-reentrant callbacks only

structure CursorSlot where
  dbHandle : Handle
  mode     : Mode                      -- internal invariant: always `.readOnly`
  rootPage : Nat
  owner    : StmtId

structure VmState where
  pc        : Nat
  regs      : Array SqlVal             -- size = prog.nRegs
  cursors   : Array (Option CursorSlot) -- size = prog.nCursors
  callDepth : Nat                      -- 0 in read-only profile (no re-entrant subprograms)
  halted    : Option IsoOutcome
```

### Internal Structural Well-Formedness vs. Deployment Policy
1. **Internal structural invariant (`WellFormed (prog : PreparedProg) : Prop`):** A bridge property—**not** a top-level input filter—that preparation establishes whenever it emits a `PreparedProg`:
   - Jump targets (`init`, `goto`, `rewind`, `next`, `seekRowid`) are `< prog.code.size`.
   - Register indices are `< prog.nRegs`; cursor indices are `< prog.nCursors`.
   - Every `callBuiltin cb` satisfies `prog.allowedCbs cb` (pure, non-reentrant, no host effects).
   - No `openWrite` or mutating `callSubprog` appears in `prog.code`.
2. **Determined deployment policy (`ReadOnlyApiProfile` / `BadEvent`):** External policy independent of any input. Even if an instruction or internal mechanism encounters an out-of-range limit, corrupt page, or error, it transitions cleanly within the profile rather than emitting `BadEvent`.

### Per-Opcode Invariant, Callbacks/Subprograms, Cleanup, and Whole-Input Discharge
- **`VmInv (prof : ReadOnlyApiProfile) (prog : PreparedProg) (st : VmState) : Prop`** (intermediate invariant for per-step lemmas):
  1. `st.halted = none → st.pc < prog.code.size` (otherwise step transitions to `.fault`).
  2. `st.regs.size = prog.nRegs` and `st.cursors.size = prog.nCursors`.
  3. **Ownership & Mode:** Every live cursor `some c` in `st.cursors` has `c.mode = .readOnly`, `c.owner = currentStmt`, and `c.dbHandle` opened read-only for `prof.protectedPath`.
  4. **Callbacks / Subprograms:** `st.callDepth = 0`; pure builtin callbacks operate only on register snapshots with no host effects; arbitrary C UDFs, triggers, and virtual-table write callbacks are excluded from the profile.
  5. **Cleanup:** `finalizeVM` closes every live cursor on every exit path (`.done`, `.err`, `.fault`), matching `Silmaril.Machine.SQLite.Handle` (`Admission.ready` / `Admission.closeOnly`), so no handle escapes or triggers post-close bad events.
- **Abstract memory invariants vs. native memory safety:** `VmInv` above is an *abstract* structural invariant over Lean `Array`s and typed handles (`pc`, `regs`, `cursors`, `callDepth`). It prevents abstract index/handle misuse inside the high-level model, but it does **not** establish native x86-64 memory safety (pointer provenance, stack/heap bounds, use-after-free freedom, or indirect-call integrity in `libsqlite3.so`), which must be proved directly at the ELF/x86-64 layer (§6).
- **Whole-input obligations across all stages (open, parsing, preparation, execution, cleanup):**
  - Per-step VM lemmas assume `WellFormed prog` and `VmInv prof prog st` as **intermediate** results.
  - The whole-input theorem (`runQuery prof input`, for **arbitrary `input : ByteArray`**) must discharge these internally across the entire lifecycle:
    1. **Connection open, parsing & preparation** (`openAndPrepare prof input : Tree IsoEvent (Except SqliteErr PreparedProg)`) satisfies `NoAttemptedBadReq prof` on every finite prefix (including read-only DB open, schema reads on arbitrary/corrupt DB bytes, error paths, or divergence), and whenever it returns `.ok prog`, it establishes `WellFormed prog` and `VmInv prof prog (initState prog)`.
    2. **Execution & cleanup** (`execVM prof prog`) preserves `VmInv` at every step and satisfies `NoAttemptedBadReq prof` on every finite prefix through finalization/close.

---

## 4. Three Core Example Theorem Statements (Pseudocode)

```lean
-- PSEUDOCODE (referencing `Silmaril.Elgot.ITree.{Tree, Trace, HasTrace, HandledTrace, Handler}`)

/-- Theorem 1: Framed Trace Safety — No Attempted Bad Request & No Committed Bad Effect.
    For ANY finite prefix `p` and ANY handler `step` obeying `HostContract prof step fsView`
    (arbitrary/corrupt DB bytes, short reads, I/O errors), neither an attempted forbidden
    request (`NoAttemptedBadReq`) nor a committed protected-FS mutation
    (`NoCommittedBadEffect`) occurs. -/
theorem framed_no_bad_thing
    (prof : ReadOnlyApiProfile) (prog : IsoProg)
    {S : Type} (step : Handler S IsoEvent) (fsView : S → HostFsView)
    (hNoBad : ∀ p, HasTrace prog p → NoAttemptedBadReq prof p)
    (hHost  : HostContract prof step fsView)
    {s0 : S} {p : Trace IsoEvent IsoOutcome}
    (hRun : HandledTrace step s0 prog p) :
    NoAttemptedBadReq prof p ∧ NoCommittedBadEffect prof step fsView s0 p

/-- Theorem 2: Per-Opcode Preservation Composes to Whole-VM `$BAD_THING` Exclusion
    (Intermediate invariant lemma; discharged by `openAndPrepare` in Theorem 3). -/
theorem vm_step_composes_to_no_bad_event
    (prof : ReadOnlyApiProfile) (prog : PreparedProg) (st0 : VmState)
    (hWF   : WellFormed prog)
    (hInv  : VmInv prof prog st0)
    (hStep : ∀ st, VmInv prof prog st → StepAvoidsBad prof prog st) :
    (∀ p, HasTrace (execVM prof prog st0) p → NoAttemptedBadReq prof p) ∧
    (∀ {S} (step : Handler S IsoEvent) s0 s1 out,
      ReturnsTo step s0 (execVM prof prog st0) s1 out → CursorsClosed out)

/-- Theorem 3: Universal Whole-Input Safety (∀ input, no input-validity premise).
    For ANY `input : ByteArray` (arbitrary SQL bytes, arbitrary length/syntax/content),
    ANY profile `prof`, and ANY host handler obeying `HostContract prof step fsView`,
    every finite execution prefix of `runQuery prof input` (open + parsing + preparation +
    VM execution + cleanup) satisfies `NoAttemptedBadReq` and `NoCommittedBadEffect`.
    Return outcome (`.done`, `.err`, `.fault`) or divergence is unconstrained. -/
theorem forall_input_no_bad_thing
    (prof : ReadOnlyApiProfile) (input : ByteArray)
    {S : Type} (step : Handler S IsoEvent) (fsView : S → HostFsView)
    (hHost : HostContract prof step fsView)
    {s0 : S} {p : Trace IsoEvent IsoOutcome}
    (hRun : HandledTrace step s0 (runQuery prof input) p) :
    NoAttemptedBadReq prof p ∧ NoCommittedBadEffect prof step fsView s0 p
```

---

## 5. Non-Vacuity Witnesses and `$BAD_THING` Refutations

Following Silmaril's pattern (`Silmaril.Machine.SqliteVfs.badShortRead`, `Silmaril.X86.Concurrency.Sqlite.Release.top_unsound`), we pair universal safety with concrete witnesses and purely synthetic refutations (**no intentional safety-violation scenario uses real exploit or attack payloads**):

1. **Non-Vacuity Witnesses (Ruling Out Trivial/Degenerate Models):**
   - *Legitimate read-only query witness:* Using `Silmaril.Machine.SQLite.VirtualMachine.pointProgram` and `Silmaril.Machine.SQLite.TrackA.Read.Interaction.vfsTree_readOnly_cold_warm`, exhibit a concrete `(prof, input, db)` where `runQuery prof input` actually executes a `.dbRead (.readPage ...)`, emits a row via `.host (.emitRow ...)`, and returns `.done 1` (plus a missed-key witness returning `.done 0`)—all satisfying `NoAttemptedBadReq` and `NoCommittedBadEffect`.
   - *Error / corrupt-page witness:* Exhibit abstract non-SELECT / syntactically invalid byte inputs and synthetic truncated/short-read DB replies whose executions produce `.err _` (or diverge) while satisfying `NoAttemptedBadReq` and `NoCommittedBadEffect`.
2. **Refutation 1 — `NoAttemptedBadReq` Without `HostContract`:**
   - Exhibit synthetic program `vis (.dbRead (.readPage h 0 4096)) (fun _ => ret (.done 0))`, which satisfies `NoAttemptedBadReq prof`, paired with a synthetic rogue handler that flips a byte of `fsView` on `.readPage`. Proves `NoAttemptedBadReq` alone does **not** imply `NoCommittedBadEffect`.
3. **Refutation 2 — Degenerate No-Op Engine (Vacuity Guard):**
   - A trivial stub `runQuery _ _ := ret (.done 0)` satisfies Theorem 3 vacuously. Ruled out by the non-vacuity witness above requiring an actual DB read and row emission.
4. **Refutation 3 — Missing Internal Invariant / Synthetic Bad Opcode:**
   - Exhibit a synthetic `PreparedProg` containing the abstract constructor `.openWrite 0 1 0` (violating `WellFormed`) whose finite trace hits `.request (.host (.writeFile ...))`, directly refuting `NoAttemptedBadReq prof` (and showing that an attempted bad request can exist even before any handler commits a host effect).
5. **Refutation 4 — Handler Contract Edge Case (Existing in Repo):**
   - `Silmaril.Machine.SqliteVfs.badShortRead` satisfies `ReadOnlyLaw` (`bad_preserves_readOnly`) yet violates `ShortReadZeroFill` and `ReadOnlyProfile` (`bad_violates_zeroFill`, `bad_not_readOnlyProfile`), showing why handler contracts must specify short-read and error behavior cleanly.

---

## 6. Connecting VM Transitions to VFS, C/ELF, and Linux Syscalls

```
Arbitrary Input (∀ SQL bytes, ∀ DB bytes)   +   ReadOnlyApiProfile (separate)
  │
  ▼  [Layers 1–3: High-Level Abstract Model — domain: sequential ITree/VM]
  Parsing & Preparation ──▶ PreparedProg (internal WellFormed) ──▶ VM (internal VmInv) ──▶ Cleanup
  │  Every finite prefix avoids `BadEvent prof` (orthogonal to done/err/fault/diverge)
  ▼  [Layer 4: Signature.Hom / Exact Lowering]
  Pager / B-Tree / VFS (`SqliteVfs.Request`, `TrackA.Read.Interaction.VfsSignature`)
  │  Enforces `SqliteVfs.ReadOnlyProfile` + `PageRead.accept`
  ▼  [Layer 5: Native C / ELF `libsqlite3.so` — OUTSTANDING NATIVE PROOF]
  x86-64 ELF (`Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So`,
              `Silmaril.Elf.Corpus.SqliteRead` @ `readDbPage` `xRead` call site)
  │  C ABI + VFS vtable dispatch (`sqlite3_io_methods.xRead`), memory/CFG safety
  ▼  [Layer 6: Linux Syscall / Process Boundary]
  Linux x86-64 Process (`Silmaril.Process.LPS`, `Silmaril.Process.TypedSyscall`,
                        `Silmaril.Process.ITreeTrace.Allows`)
  │  Discharges `HostContract`: only `openat(O_RDONLY)`, `pread64`/`read`, `fstat`, `close`,
  │  `write` to stdout/stderr (fd 1/2), non-exec anonymous `mmap`/`brk`
  ▼  [Layers 7–8: Two ELF Clients]
  Client A: `sqlite3 -batch -readonly ...`     Client B: Independent C client (`sqlite3_open_v2(RO)`)
```

- **Abstract model domain vs. outstanding native proof:** Layers 1–4 operate over an abstract sequential ITree/VM/VFS model. Proving `forall_input_no_bad_thing` at Layers 1–4 establishes the specification and proof structure, **not** native safety of `libsqlite3.so`. The outstanding native proof (Layers 5–8) must show that every reachable x86-64 execution of `libsqlite3.so` (and each client binary) on arbitrary input bytes refines the profile-confined syscall/VFS boundary without memory corruption, control-flow hijack, or unmodeled syscalls—without assuming away malformed SQL or corrupt DB bytes.
- **Concrete bridge points already in repo:**
  - VM → VFS: `Silmaril.Elgot.ITree.Exact.Signature.Hom` and `TrackA.Interaction.Signature.Hom` lower `IsoEvent.dbRead` to `Silmaril.Machine.SqliteVfs.Request`.
  - VFS → ELF: `Silmaril.Elf.Corpus.SqliteRead` already proves x86-64 dispatch at the non-WAL `xRead` call site inside `readDbPage` (`run_dispatch`, `buffer_unchanged`, `sound`), stopping at handler entry.
  - ELF → Syscalls: `Silmaril.Process.LPS` + `Silmaril.Process.TypedSyscall` + `Silmaril.Process.ITreeTrace.Allows` connect native execution to a syscall allowlist and filesystem nonmutation contract.

---

## 7. Layer Ownership, Status, Deliverables, and Two-Client Reuse

| Layer | Existing Repo Namespaces | Status | Primary Proof Obligations | Owner Role | Directional Short Deliverables |
|---|---|---|---|---|---|
| **1. ITree & `$BAD_THING` Policy** | `Silmaril.Elgot.ITree`, `ExactITree`, `Process.ITreeTrace`, `TrackA.Interaction` | **Landed (core)**; Isolation layer **In Progress (Sibling Task 1)** | Define `IsoEvent`, `ReadOnlyApiProfile`, `BadEvent`, `NoAttemptedBadReq`, `NoCommittedBadEffect`, `HostContract`; prove Theorem 1 + Refutation 1 | Semantics / ITree | `SqliteIso` event/`BadEvent`/profile header, framed prefix safety theorem, synthetic rogue-handler refutation |
| **2. Prepared VM** | `Formats.Sqlite.Vdbe`, `Machine.SQLite.VirtualMachine.{Defs,Traced,Mutable}`, `Handle` | **Landed (point core)**; Prepared VM **In Progress (Sibling Task 2)** | `PreparedProg`, internal `WellFormed` & abstract `VmInv`, per-opcode preservation, cleanup on all exits, Theorem 2 + Refutation 3 | VM / Semantics | Prepared VM + per-opcode → `execVM` `$BAD_THING` exclusion, positive & negative witnesses |
| **3. Open, Parsing & Preparation** | `Machine.SQLite.{Tokenizer,Parser,CodeGenerator,CommandProcessor}`, `Semantics.SQLite.Relational` | **Landed (narrow SELECT)**; Universal arbitrary-input safety **Planned** | For **∀ `input : ByteArray`**, prove open/parsing/preparation satisfies `NoAttemptedBadReq` and discharges `WellFormed`/`VmInv` on any emitted program (Theorem 3) | Frontend / Compiler | Total `openAndPrepare` over arbitrary `ByteArray`, whole-input Theorem 3 + non-vacuity witness |
| **4. B-Tree / Pager / VFS** | `Machine.SqliteVfs`, `Machine.SQLite.TrackA.Read.Interaction`, `Containers.SqliteVfs` | **Landed (single-file RO VFS + leaf read)**; Arbitrary-byte handling **Planned** | Lower `IsoEvent.dbRead` to `SqliteVfs.Request`; prove arbitrary corrupt/short-read bytes never trigger `BadEvent` | Backend / Storage | `Signature.Hom` to `VfsSignature`; arbitrary-DB-byte prefix safety proofs |
| **5. Native `libsqlite3.so` ELF** | `Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So`, `Elf.Corpus.{SqliteRead,SqliteMutex,SqliteGlobalVersion}`, `X86.*` | **Landed (staged ELF + `xRead`/mutex/version cuts)**; Whole-API safety **Planned** | Discharge native memory/CFG safety, read-only flag & VFS vtable confinement across `sqlite3_open_v2`/`prepare_v2`/`step`/`finalize`/`close` for ∀ inputs | Native ELF / x86-64 | Expand from `readDbPage` `xRead` cut to `sqlite3_open_v2(RO)` + VFS method-table & prepare/step confinement |
| **6. Linux Syscalls & Process** | `Process.LPS`, `Process.TypedSyscall`, `Process.ITreeTrace`, `Process.CLI.X86Linux` | **Landed (LPS + typed syscall allowlist)**; SQLite wiring **Planned** | Prove allowed Linux syscalls under `O_RDONLY` satisfy `HostContract` (no protected FS mutation) | Process / OS | Syscall-level `ReadOnlyFsContract` over `Process.LPS.Fs` + `ITreeTrace.Allows` bridge |
| **7. Client 1: Batch Shell (`sqlite3`)** | `Elf.Staged.Corpus.Sqlite.X8664.Sqlite3`, `Cli.Spec.SqliteShell` | **Landed (staged ELF + CLI spec)**; Shell confinement **Planned** | For ∀ stdin/SQL input under `-batch -readonly`, prove no dot-command escape (`.shell`, `.output`, `.load`, `.open`) triggers `BadEvent` and calls stay within `libsqlite3.so` contract | CLI / Client | Shell-frontend `$BAD_THING` exclusion spec + wrapper proof reusing Layers 1–6 |
| **8. Client 2: Independent C Client** | (New thin C driver + `Elf.Staged` target; reuses `Libsqlite3So` + `Process.LPS`) | **Planned** | For ∀ input bytes, prove C `main` configures `SQLITE_OPEN_READONLY` (and profile guards), invokes `libsqlite3.so`, and writes only to stdout/stderr | Native / Client | Minimal pinned C client ELF + small wrapper proof reusing 100% of Layers 1–6 |

### Platform & Two-Client Reuse Strategy
Layers 1–6 establish the **shared library contract** for `libsqlite3.so` parameterized by `ReadOnlyApiProfile` and `HostContract`. Both ELF clients reuse this proof stack:
- **Independent C client (lowest-risk first native end-to-end target):** Thin, auditable C harness (~100 LOC) that configures `SQLITE_OPEN_READONLY` and routes arbitrary input bytes to `libsqlite3.so`; client proof covers only the harness setup and stdout/stderr output.
- **Upstream batch shell (`sqlite3`):** Reuses the same `libsqlite3.so` contract and adds a dedicated **shell-frontend confinement proof** showing that under `-batch -readonly` (with controlled environment / no `.sqliterc`, matching `Silmaril.Cli.Spec.SqliteShell.Shell.args`), arbitrary input lines cannot trigger shell-level `$BAD_THING` (`.shell`, `.system`, `.output`, `.save`, `.load`, `.open`).
