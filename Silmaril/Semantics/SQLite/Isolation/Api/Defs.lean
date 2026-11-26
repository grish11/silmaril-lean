module

public import Silmaril.Semantics.ITree.Trace.Handled.Defs

/-!
# Restricted SQLite API Isolation Model (Interaction-Tree Abstraction)

This module defines a **restricted, high-level interaction-tree abstraction** of
a single-connection, single-thread SQLite API and host effect boundary, built on
Silmaril's weak interaction trees (`Silmaril.Elgot.ITree` in
`Silmaril/Semantics/ITree/Defs.lean`, `Trace/Defs.lean`, `Reindex/Defs.lean`,
and `Trace/Handled/Defs.lean`).

## Scope and explicit non-claims
- **Target abstraction**: finite-prefix observational safety (no forbidden DB or
  host events) and protected-state preservation under an explicit handler frame
  contract, for arbitrary potentially untrusted SQL strings and nondeterministic
  handler responses (including errors and rejections).
- **Not vacuous**: forbidden operations (`writeDb`, `attachDb`, `loadExtension`,
  `hostEffect`, read-write `openDb`, and access to non-allowed databases) are
  explicitly representable in `ApiEvent`. Safety is established either by
  program construction or by explicit denial at the public boundary
  (`guardedCall`), and contrasted with negative witnesses.
- **Honest non-mutation**: absence of forbidden events in traces (`TreeSafe` /
  `HandledTreeSafe`) does not by itself imply state equality; protected-state
  preservation additionally requires an explicit handler frame condition
  (`FrameContract`).
- **Non-claims**: this high-level model does **not** prove query-result
  correctness, confidentiality, termination, blanket resource bounds, security
  of real `libsqlite3.so`, or C / x86-64 ELF refinement.
-/

@[expose] public section

namespace Silmaril.SQLite.Isolation.Api

open Silmaril.Elgot

/-- Identifier of a database target at the abstract SQLite API boundary. -/
structure DbId where
  name : String
  deriving DecidableEq, Repr

/-- Abstract connection handle returned by a successful open. -/
structure ConnHandle where
  id : Nat
  deriving DecidableEq, Repr

/-- Abstract prepared-statement handle returned by a successful prepare. -/
structure StmtHandle where
  id : Nat
  deriving DecidableEq, Repr

/-- Requested database open mode at the abstract API boundary. -/
inductive OpenMode where
  | readOnly
  | readWrite
  deriving DecidableEq, Repr

/-- Categories of forbidden or unmodeled host effects outside the read-only
SQLite API profile. -/
inductive HostEffectKind where
  | fileWrite (path : String)
  | network (endpoint : String)
  | processExec (command : String)
  | unmodeled (label : String)
  deriving DecidableEq, Repr

/-- Reasons the public API boundary may deny a request before invoking the
underlying handler. -/
inductive DenyReason where
  | wrongDatabase
  | writeModeForbidden
  | writeForbidden
  | attachForbidden
  | extensionForbidden
  | hostEffectForbidden
  deriving DecidableEq, Repr

/-- Errors observable at the abstract SQLite API boundary, including malformed
SQL input, invalid handles, backend I/O failures, busy responses, and explicit
policy denial. -/
inductive ApiError where
  | malformedSql
  | invalidHandle
  | ioError
  | busy
  | denied (reason : DenyReason)
  deriving DecidableEq, Repr

/-- Abstract row payload returned by a read step. -/
abbrev RowData := List UInt8

/-- Result of stepping a prepared read statement. -/
inductive StepOutcome where
  | row (data : RowData)
  | done
  deriving DecidableEq, Repr

/-- Explicit authority/capability profile for a single-connection SQLite API
session. -/
structure AuthorityProfile where
  allowedDb : DbId
  allowReadOnlyOpen : Bool := true
  allowReadWriteOpen : Bool := false
  allowRead : Bool := true
  allowWrite : Bool := false
  allowAttach : Bool := false
  allowLoadExtension : Bool := false
  allowHostEffect : Bool := false
  deriving DecidableEq, Repr

/-- Canonical read-only authority profile for one identified database `db`:
permits read-only open, prepare, read-step, finalize, and close on `db`;
forbids read-write open, writes, `ATTACH`, extension loading, access to any
other database, and unmodeled host effects. -/
def readOnlyProfile (db : DbId) : AuthorityProfile where
  allowedDb := db

/-- Restricted high-level SQLite API and host effect signature.
Typed requests carry their exact reply types. Forbidden operations are
explicitly representable so policy enforcement and negative witnesses are
meaningful. -/
inductive ApiEvent : Type → Type where
  | openDb (db : DbId) (mode : OpenMode) : ApiEvent (Except ApiError ConnHandle)
  | prepare (conn : ConnHandle) (db : DbId) (sql : String) :
      ApiEvent (Except ApiError StmtHandle)
  | stepRead (stmt : StmtHandle) (db : DbId) :
      ApiEvent (Except ApiError StepOutcome)
  | finalize (stmt : StmtHandle) : ApiEvent (Except ApiError Unit)
  | closeDb (conn : ConnHandle) : ApiEvent (Except ApiError Unit)
  | writeDb (conn : ConnHandle) (db : DbId) (offset : Nat) (bytes : List UInt8) :
      ApiEvent (Except ApiError Unit)
  | attachDb (conn : ConnHandle) (target : DbId) (schemaName : String) :
      ApiEvent (Except ApiError Unit)
  | loadExtension (conn : ConnHandle) (path : String) :
      ApiEvent (Except ApiError Unit)
  | hostEffect (kind : HostEffectKind) : ApiEvent (Except ApiError Unit)

/-- Weak interaction tree over the restricted SQLite API effect signature. -/
abbrev ApiTree (A : Type) := ITree.Tree ApiEvent A

/-- Finite-prefix trace over `ApiEvent`. -/
abbrev ApiTrace (A : Type) := ITree.Trace ApiEvent A

/-- Nondeterministic relational handler for `ApiEvent` over abstract state `S`. -/
abbrev ApiHandler (S : Type) := ITree.Handler S ApiEvent

/-- Decide whether an API request is permitted by `profile`, returning a
concrete `DenyReason` when rejected. -/
def checkEvent (profile : AuthorityProfile) :
    {R : Type} → ApiEvent R → Except DenyReason Unit
  | _, .openDb db .readOnly =>
      if db = profile.allowedDb && profile.allowReadOnlyOpen then .ok ()
      else .error .wrongDatabase
  | _, .openDb db .readWrite =>
      if db = profile.allowedDb && profile.allowReadWriteOpen then .ok ()
      else if db ≠ profile.allowedDb then .error .wrongDatabase
      else .error .writeModeForbidden
  | _, .prepare _ db _ =>
      if db = profile.allowedDb && profile.allowRead then .ok ()
      else .error .wrongDatabase
  | _, .stepRead _ db =>
      if db = profile.allowedDb && profile.allowRead then .ok ()
      else .error .wrongDatabase
  | _, .finalize _ => .ok ()
  | _, .closeDb _ => .ok ()
  | _, .writeDb _ db _ _ =>
      if db = profile.allowedDb && profile.allowWrite then .ok ()
      else if db ≠ profile.allowedDb then .error .wrongDatabase
      else .error .writeForbidden
  | _, .attachDb _ _ _ =>
      if profile.allowAttach then .ok ()
      else .error .attachForbidden
  | _, .loadExtension _ _ =>
      if profile.allowLoadExtension then .ok ()
      else .error .extensionForbidden
  | _, .hostEffect _ =>
      if profile.allowHostEffect then .ok ()
      else .error .hostEffectForbidden

/-- Predicate stating that a packed `ApiEvent` request is permitted by `profile`. -/
def EventAllowed (profile : AuthorityProfile) (q : ITree.Request ApiEvent) : Prop :=
  checkEvent profile q.2 = .ok ()

instance (profile : AuthorityProfile) (q : ITree.Request ApiEvent) :
    Decidable (EventAllowed profile q) :=
  match h : checkEvent profile q.2 with
  | .ok () => isTrue h
  | .error _ => isFalse (by simp [EventAllowed, h])

/-- Finite-prefix observational safety: every pending request or completed
exchange in `p` is permitted by `profile`. -/
def TraceSafe {A : Type} (profile : AuthorityProfile) : ApiTrace A → Prop
  | .prefix => True
  | .result _ => True
  | .request e => EventAllowed profile ⟨_, e⟩
  | .exchange e _ tail => EventAllowed profile ⟨_, e⟩ ∧ TraceSafe profile tail

/-- Unconditional tree safety: every finite observation (including pending
requests and non-terminating prefixes) of `t` satisfies `TraceSafe profile`. -/
def TreeSafe {A : Type} (profile : AuthorityProfile) (t : ApiTree A) : Prop :=
  ∀ p, ITree.HasTrace t p → TraceSafe profile p

/-- Handler-scoped tree safety: every finite observation of `t` admitted by
`step` from initial state `s` satisfies `TraceSafe profile`. -/
def HandledTreeSafe {S A : Type} (profile : AuthorityProfile)
    (step : ApiHandler S) (s : S) (t : ApiTree A) : Prop :=
  ∀ p, ITree.HandledTrace step s t p → TraceSafe profile p

/-- Explicit handler frame contract: every request permitted by `profile`
preserves the projected protected state `protectedState` across every admitted
handler transition. -/
def FrameContract {S P : Type} (profile : AuthorityProfile)
    (step : ApiHandler S) (protectedState : S → P) : Prop :=
  ∀ (q : ITree.Request ApiEvent) (s s' : S) (r : q.1),
    EventAllowed profile q →
    step q s r s' →
    protectedState s' = protectedState s

/-- Replay of a finite trace `p` from state `s` reaching post-prefix state `s'`.
This captures intermediate states along partial or non-terminating prefixes as
well as completed runs. -/
def ReplayTo {S A : Type} (step : ApiHandler S) : S → ApiTrace A → S → Prop
  | s, .prefix, s' => s' = s
  | s, .request _, s' => s' = s
  | s, .result _, s' => s' = s
  | s, .exchange e r tail, s' =>
      ∃ mid, step ⟨_, e⟩ s r mid ∧ ReplayTo step mid tail s'

/-- Issue a single raw (unguarded) API event and return its handler reply. -/
def rawCall {R : Type} (e : ApiEvent R) : ApiTree R :=
  ITree.vis e ITree.ret

/-- Public API boundary wrapper: checks `profile` before issuing `e`.
If `e` is forbidden under `profile`, the boundary denies the request and
returns `.error (.denied reason)` without emitting any visible event. -/
def guardedCall {R : Type} (profile : AuthorityProfile)
    (e : ApiEvent (Except ApiError R)) : ApiTree (Except ApiError R) :=
  match checkEvent profile e with
  | .ok () => ITree.vis e ITree.ret
  | .error reason => ITree.ret (.error (.denied reason))

/-! ## Worked sessions, negative witnesses, and reference handlers -/

/-- Realistic single-connection read-only SQLite API session:
open `db` read-only, prepare an arbitrary (potentially untrusted) SQL string,
step-read once, finalize, and close — propagating handler errors and closing
opened handles on failure paths. -/
def openReadCloseSession (db : DbId) (sql : String) :
    ApiTree (Except ApiError (Option RowData)) := do
  match ← rawCall (.openDb db .readOnly) with
  | .error err => pure (.error err)
  | .ok conn =>
    match ← rawCall (.prepare conn db sql) with
    | .error err =>
      let _ ← rawCall (.closeDb conn)
      pure (.error err)
    | .ok stmt =>
      let stepRes ← rawCall (.stepRead stmt db)
      let _ ← rawCall (.finalize stmt)
      let _ ← rawCall (.closeDb conn)
      match stepRes with
      | .error err => pure (.error err)
      | .ok .done => pure (.ok none)
      | .ok (.row data) => pure (.ok (some data))

/-- A session routed through the public boundary `guardedCall` that opens `db`
read-only, attempts a forbidden write (denied at the boundary), and safely
closes the connection. -/
def guardedDeniedWriteSession (db : DbId) (offset : Nat) (bytes : List UInt8) :
    ApiTree (Except ApiError Unit) := do
  let profile := readOnlyProfile db
  match ← guardedCall profile (.openDb db .readOnly) with
  | .error err => pure (.error err)
  | .ok conn =>
    let writeRes ← guardedCall profile (.writeDb conn db offset bytes)
    let _ ← guardedCall profile (.closeDb conn)
    pure writeRes

/-- Negative witness: unguarded DB write request. -/
def unsafeWriteProgram (conn : ConnHandle) (db : DbId) (offset : Nat) (bytes : List UInt8) :
    ApiTree (Except ApiError Unit) :=
  rawCall (.writeDb conn db offset bytes)

/-- Negative witness: unguarded `ATTACH DATABASE` request. -/
def unsafeAttachProgram (conn : ConnHandle) (target : DbId) (schemaName : String) :
    ApiTree (Except ApiError Unit) :=
  rawCall (.attachDb conn target schemaName)

/-- Negative witness: unguarded extension-loading request. -/
def unsafeLoadExtensionProgram (conn : ConnHandle) (path : String) :
    ApiTree (Except ApiError Unit) :=
  rawCall (.loadExtension conn path)

/-- Negative witness: unguarded host effect request. -/
def unsafeHostEffectProgram (kind : HostEffectKind) :
    ApiTree (Except ApiError Unit) :=
  rawCall (.hostEffect kind)

/-- Negative witness: unguarded read-write open request. -/
def unsafeReadWriteOpenProgram (db : DbId) :
    ApiTree (Except ApiError ConnHandle) :=
  rawCall (.openDb db .readWrite)

/-- Negative witness: unguarded open of another database. -/
def unsafeWrongDbOpenProgram (otherDb : DbId) :
    ApiTree (Except ApiError ConnHandle) :=
  rawCall (.openDb otherDb .readOnly)

/-- Concrete abstract state for a single-connection reference handler witness. -/
structure ReferenceState where
  protectedDb : DbId → List UInt8
  openConn : Option (ConnHandle × DbId × OpenMode) := none
  openStmt : Option (StmtHandle × ConnHandle × DbId) := none
  nextId : Nat := 0

/-- A nondeterministic single-connection reference handler:
- On `openDb db .readOnly`, `prepare`, `stepRead`, `finalize`, `closeDb`, it may
  succeed or return arbitrary backend errors while leaving `protectedDb` unchanged.
- On `writeDb`, it is permitted to mutate `protectedDb` (showing `FrameContract`
  is non-trivial: the handler *can* write when given a write event, yet preserves
  `protectedDb` for all events allowed by `readOnlyProfile`). -/
def referenceHandler : ApiHandler ReferenceState
  | ⟨_, .openDb db mode⟩, s, reply, s' =>
      match reply with
      | .error _ => s' = s
      | .ok h =>
          s.openConn = none ∧
          h = ⟨s.nextId⟩ ∧
          s' = { s with openConn := some (h, db, mode), nextId := s.nextId + 1 }
  | ⟨_, .prepare conn db _⟩, s, reply, s' =>
      match reply with
      | .error _ => s' = s
      | .ok stmt =>
          (∃ mode, s.openConn = some (conn, db, mode)) ∧
          s.openStmt = none ∧
          stmt = ⟨s.nextId⟩ ∧
          s' = { s with openStmt := some (stmt, conn, db), nextId := s.nextId + 1 }
  | ⟨_, .stepRead stmt db⟩, s, reply, s' =>
      match reply with
      | .error _ => s' = s
      | .ok _ =>
          (∃ conn, s.openStmt = some (stmt, conn, db)) ∧
          s' = s
  | ⟨_, .finalize stmt⟩, s, reply, s' =>
      match reply with
      | .error _ => s' = s
      | .ok () =>
          (∃ conn db, s.openStmt = some (stmt, conn, db)) ∧
          s' = { s with openStmt := none }
  | ⟨_, .closeDb conn⟩, s, reply, s' =>
      match reply with
      | .error _ => s' = s
      | .ok () =>
          (∃ db mode, s.openConn = some (conn, db, mode)) ∧
          s' = { s with openConn := none, openStmt := none }
  | ⟨_, .writeDb _ db _ bytes⟩, s, reply, s' =>
      match reply with
      | .error _ => s' = s
      | .ok () =>
          s' = { s with protectedDb := fun d => if d = db then bytes else s.protectedDb d }
  | ⟨_, .attachDb _ _ _⟩, s, reply, s' =>
      reply = .error (.denied .attachForbidden) ∧ s' = s
  | ⟨_, .loadExtension _ _⟩, s, reply, s' =>
      reply = .error (.denied .extensionForbidden) ∧ s' = s
  | ⟨_, .hostEffect _⟩, s, reply, s' =>
      reply = .error (.denied .hostEffectForbidden) ∧ s' = s

/-- Honesty witness: a dishonest handler that mutates its state (`Nat`) even on
an allowed read-only `openDb` request, violating `FrameContract`. -/
def dishonestHandler : ApiHandler Nat
  | ⟨_, .openDb _ .readOnly⟩, n, reply, n' => reply = .ok ⟨n⟩ ∧ n' = n + 1
  | _, n, _, n' => n' = n

end Silmaril.SQLite.Isolation.Api
