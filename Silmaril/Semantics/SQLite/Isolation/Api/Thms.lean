module

public import Silmaril.Semantics.SQLite.Isolation.Api.Defs
public import Silmaril.Semantics.ITree.Trace.Handled.Thms
import Silmaril.Proofs.Semantics.SQLite.Isolation.Api.Safety

/-!
# Theorems for the Restricted SQLite API Isolation Model

Public theorem header for `Silmaril.Semantics.SQLite.Isolation.Api`.
Longer proofs live in `Silmaril.Proofs.Semantics.SQLite.Isolation.Api.Safety`.

This module establishes:
1. Exact characterization of `readOnlyProfile` permissions and denials.
2. Compositional finite-prefix safety laws (`ret`, `diverge`, `vis`, `rawCall`,
   `guardedCall`, `bind`, trace-inclusion monotonicity, and handler-scoped
   `HandledTreeSafe` sequencing).
3. Honest protected-state preservation under an explicit `FrameContract`, both
   for arbitrary finite prefixes (`ReplayTo`, covering partial/non-terminating
   runs) and for completed returns (`ITree.ReturnsTo`).
4. Worked safety and state-preservation proofs for `openReadCloseSession` (over
   arbitrary SQL strings and nondeterministic handlers) and
   `guardedDeniedWriteSession` (boundary denial), together with negative
   witnesses for unguarded forbidden operations and a dishonesty witness showing
   why `FrameContract` is required.
-/

public section

namespace Silmaril.SQLite.Isolation.Api

open Silmaril.Elgot
open Silmaril.Proofs.Semantics.SQLite.Isolation.Api

/-! ## `readOnlyProfile` permission characterization -/

@[simp] theorem eventAllowed_readOnly_openDb_readOnly (db target : DbId) :
    EventAllowed (readOnlyProfile db) ⟨_, .openDb target .readOnly⟩ ↔ target = db := by
  by_cases h : target = db <;> simp [EventAllowed, checkEvent, readOnlyProfile, h]

@[simp] theorem eventAllowed_readOnly_openDb_readWrite (db target : DbId) :
    ¬ EventAllowed (readOnlyProfile db) ⟨_, .openDb target .readWrite⟩ := by
  by_cases h : target = db <;> simp [EventAllowed, checkEvent, readOnlyProfile, h]

@[simp] theorem eventAllowed_readOnly_prepare (db target : DbId)
    (conn : ConnHandle) (sql : String) :
    EventAllowed (readOnlyProfile db) ⟨_, .prepare conn target sql⟩ ↔ target = db := by
  by_cases h : target = db <;> simp [EventAllowed, checkEvent, readOnlyProfile, h]

@[simp] theorem eventAllowed_readOnly_stepRead (db target : DbId) (stmt : StmtHandle) :
    EventAllowed (readOnlyProfile db) ⟨_, .stepRead stmt target⟩ ↔ target = db := by
  by_cases h : target = db <;> simp [EventAllowed, checkEvent, readOnlyProfile, h]

@[simp] theorem eventAllowed_readOnly_finalize (db : DbId) (stmt : StmtHandle) :
    EventAllowed (readOnlyProfile db) ⟨_, .finalize stmt⟩ := by
  simp [EventAllowed, checkEvent]

@[simp] theorem eventAllowed_readOnly_closeDb (db : DbId) (conn : ConnHandle) :
    EventAllowed (readOnlyProfile db) ⟨_, .closeDb conn⟩ := by
  simp [EventAllowed, checkEvent]

@[simp] theorem eventAllowed_readOnly_writeDb (db target : DbId) (conn : ConnHandle)
    (offset : Nat) (bytes : List UInt8) :
    ¬ EventAllowed (readOnlyProfile db) ⟨_, .writeDb conn target offset bytes⟩ := by
  by_cases h : target = db <;> simp [EventAllowed, checkEvent, readOnlyProfile, h]

@[simp] theorem eventAllowed_readOnly_attachDb (db target : DbId) (conn : ConnHandle)
    (schemaName : String) :
    ¬ EventAllowed (readOnlyProfile db) ⟨_, .attachDb conn target schemaName⟩ := by
  simp [EventAllowed, checkEvent, readOnlyProfile]

@[simp] theorem eventAllowed_readOnly_loadExtension (db : DbId) (conn : ConnHandle)
    (path : String) :
    ¬ EventAllowed (readOnlyProfile db) ⟨_, .loadExtension conn path⟩ := by
  simp [EventAllowed, checkEvent, readOnlyProfile]

@[simp] theorem eventAllowed_readOnly_hostEffect (db : DbId) (kind : HostEffectKind) :
    ¬ EventAllowed (readOnlyProfile db) ⟨_, .hostEffect kind⟩ := by
  simp [EventAllowed, checkEvent, readOnlyProfile]

/-! ## Compositional finite-prefix safety and sequencing laws -/

theorem treeSafe_ret {A : Type} (profile : AuthorityProfile) (a : A) :
    TreeSafe profile (ITree.ret a) :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.treeSafe_ret profile a

theorem treeSafe_pure {A : Type} (profile : AuthorityProfile) (a : A) :
    TreeSafe profile (pure a : ApiTree A) :=
  treeSafe_ret profile a

theorem treeSafe_diverge {A : Type} (profile : AuthorityProfile) :
    TreeSafe profile (ITree.diverge : ApiTree A) :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.treeSafe_diverge profile

theorem treeSafe_vis {R A : Type} {profile : AuthorityProfile}
    {e : ApiEvent R} {k : R → ApiTree A}
    (he : EventAllowed profile ⟨R, e⟩)
    (hk : ∀ r, TreeSafe profile (k r)) :
    TreeSafe profile (ITree.vis e k) :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.treeSafe_vis he hk

theorem treeSafe_rawCall {R : Type} {profile : AuthorityProfile} {e : ApiEvent R}
    (he : EventAllowed profile ⟨R, e⟩) :
    TreeSafe profile (rawCall e) :=
  treeSafe_vis he (fun r => treeSafe_ret profile r)

/-- Any call routed through the public boundary `guardedCall` is safe under
`profile`: forbidden requests are denied before any visible event is emitted. -/
theorem treeSafe_guardedCall {R : Type} (profile : AuthorityProfile)
    (e : ApiEvent (Except ApiError R)) :
    TreeSafe profile (guardedCall profile e) :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.treeSafe_guardedCall profile e

/-- Reusable monadic sequencing (`bind`) law for unconditional tree safety. -/
theorem treeSafe_bind {A B : Type} {profile : AuthorityProfile}
    {t : ApiTree A} {k : A → ApiTree B}
    (ht : TreeSafe profile t)
    (hk : ∀ a, TreeSafe profile (k a)) :
    TreeSafe profile (t >>= k) :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.treeSafe_bind ht hk

/-- Finite-trace refinement (`ITree.TraceLE`) preserves tree safety downward. -/
theorem treeSafe_mono {A : Type} {profile : AuthorityProfile} {t s : ApiTree A}
    (hle : ITree.TraceLE t s) (hs : TreeSafe profile s) :
    TreeSafe profile t :=
  fun p hp => hs p (hle p hp)

/-- Unconditional tree safety implies handler-scoped safety for every
nondeterministic handler `step` and initial state `s`. -/
theorem treeSafe_to_handled {S A : Type} {profile : AuthorityProfile}
    (step : ApiHandler S) (s : S) {t : ApiTree A} (ht : TreeSafe profile t) :
    HandledTreeSafe profile step s t :=
  fun p hp => ht p hp.1

theorem handledTreeSafe_mono {S A : Type} {profile : AuthorityProfile}
    {step : ApiHandler S} {s : S} {t u : ApiTree A}
    (hle : ITree.HandledTraceLE step s t u) (hu : HandledTreeSafe profile step s u) :
    HandledTreeSafe profile step s t :=
  fun p hp => hu p (hle p hp)

theorem handledTreeSafe_ret {S A : Type} (profile : AuthorityProfile)
    (step : ApiHandler S) (s : S) (a : A) :
    HandledTreeSafe profile step s (ITree.ret a) :=
  treeSafe_to_handled step s (treeSafe_ret profile a)

/-- Handler-scoped single-transition safety law. -/
theorem handledTreeSafe_vis {S R A : Type} {profile : AuthorityProfile}
    {step : ApiHandler S} {s : S} {e : ApiEvent R} {k : R → ApiTree A}
    (he : EventAllowed profile ⟨R, e⟩)
    (hk : ∀ r s', step ⟨R, e⟩ s r s' → HandledTreeSafe profile step s' (k r)) :
    HandledTreeSafe profile step s (ITree.vis e k) :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.handledTreeSafe_vis he hk

/-- Reusable handler-scoped sequencing (`bind`) law: the continuation only needs
to be safe at states `y` and values `a` reachable via `ITree.ReturnsTo`. -/
theorem handledTreeSafe_bind {S A B : Type} {profile : AuthorityProfile}
    {step : ApiHandler S} {s : S} {t : ApiTree A} {k : A → ApiTree B}
    (ht : HandledTreeSafe profile step s t)
    (hk : ∀ y a, ITree.ReturnsTo step s t y a → HandledTreeSafe profile step y (k a)) :
    HandledTreeSafe profile step s (t >>= k) :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.handledTreeSafe_bind ht hk

/-! ## Handler frame condition and protected-state preservation -/

theorem replayTo_iff_replay {S A : Type} (step : ApiHandler S) (s : S) (p : ApiTrace A) :
    (∃ s', ReplayTo step s p s') ↔ ITree.Replay step s p :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.replayTo_iff_replay step s p

/-- Every safe finite prefix replayed under a frame-respecting handler preserves
the protected state projection. -/
theorem replayTo_preserves_protected {S P A : Type} {profile : AuthorityProfile}
    {step : ApiHandler S} {protectedState : S → P}
    (hframe : FrameContract profile step protectedState)
    {s s' : S} {p : ApiTrace A}
    (hsafe : TraceSafe profile p)
    (hrep : ReplayTo step s p s') :
    protectedState s' = protectedState s :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.replayTo_preserves_protected hframe hsafe hrep

/-- Every finite prefix (including partial or non-terminating prefixes) of a
handler-safe tree preserves `protectedState` under `FrameContract`. -/
theorem handled_prefix_preserves_protected {S P A : Type} {profile : AuthorityProfile}
    {step : ApiHandler S} {protectedState : S → P}
    (hframe : FrameContract profile step protectedState)
    {s s' : S} {t : ApiTree A} {p : ApiTrace A}
    (hsafe : HandledTreeSafe profile step s t)
    (htrace : ITree.HasTrace t p)
    (hrep : ReplayTo step s p s') :
    protectedState s' = protectedState s :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.handled_prefix_preserves_protected
    hframe hsafe htrace hrep

/-- Unconditional tree safety plus `FrameContract` preserves `protectedState`
across every finite prefix. -/
theorem treeSafe_prefix_preserves_protected {S P A : Type} {profile : AuthorityProfile}
    {step : ApiHandler S} {protectedState : S → P}
    (hframe : FrameContract profile step protectedState)
    {s s' : S} {t : ApiTree A} {p : ApiTrace A}
    (hsafe : TreeSafe profile t)
    (htrace : ITree.HasTrace t p)
    (hrep : ReplayTo step s p s') :
    protectedState s' = protectedState s :=
  handled_prefix_preserves_protected hframe (treeSafe_to_handled step s hsafe) htrace hrep

/-- Every completed return (`ITree.ReturnsTo`) of a handler-safe tree preserves
`protectedState` under `FrameContract`. -/
theorem handled_returnsTo_preserves_protected {S P A : Type} {profile : AuthorityProfile}
    {step : ApiHandler S} {protectedState : S → P}
    (hframe : FrameContract profile step protectedState)
    {s s' : S} {t : ApiTree A} {a : A}
    (hsafe : HandledTreeSafe profile step s t)
    (hret : ITree.ReturnsTo step s t s' a) :
    protectedState s' = protectedState s :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.handled_returnsTo_preserves_protected
    hframe hsafe hret

/-- Unconditional tree safety plus `FrameContract` preserves `protectedState`
across every completed return. -/
theorem treeSafe_returnsTo_preserves_protected {S P A : Type} {profile : AuthorityProfile}
    {step : ApiHandler S} {protectedState : S → P}
    (hframe : FrameContract profile step protectedState)
    {s s' : S} {t : ApiTree A} {a : A}
    (hsafe : TreeSafe profile t)
    (hret : ITree.ReturnsTo step s t s' a) :
    protectedState s' = protectedState s :=
  handled_returnsTo_preserves_protected hframe (treeSafe_to_handled step s hsafe) hret

/-! ## Worked open/read/close session and public boundary denial -/

/-- The realistic open/prepare/stepRead/finalize/close session is safe under
`readOnlyProfile db` for every arbitrary (potentially untrusted) SQL string. -/
theorem openReadCloseSession_safe (db : DbId) (sql : String) :
    TreeSafe (readOnlyProfile db) (openReadCloseSession db sql) :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.openReadCloseSession_safe db sql

theorem openReadCloseSession_prefix_preserves_protected {S P : Type}
    {step : ApiHandler S} {protectedState : S → P}
    (db : DbId) (sql : String)
    (hframe : FrameContract (readOnlyProfile db) step protectedState)
    {s s' : S} {p : ApiTrace (Except ApiError (Option RowData))}
    (htrace : ITree.HasTrace (openReadCloseSession db sql) p)
    (hrep : ReplayTo step s p s') :
    protectedState s' = protectedState s :=
  treeSafe_prefix_preserves_protected hframe (openReadCloseSession_safe db sql) htrace hrep

theorem openReadCloseSession_returnsTo_preserves_protected {S P : Type}
    {step : ApiHandler S} {protectedState : S → P}
    (db : DbId) (sql : String)
    (hframe : FrameContract (readOnlyProfile db) step protectedState)
    {s s' : S} {res : Except ApiError (Option RowData)}
    (hret : ITree.ReturnsTo step s (openReadCloseSession db sql) s' res) :
    protectedState s' = protectedState s :=
  treeSafe_returnsTo_preserves_protected hframe (openReadCloseSession_safe db sql) hret

@[simp] theorem guardedCall_write_denied (db : DbId) (conn : ConnHandle)
    (offset : Nat) (bytes : List UInt8) :
    guardedCall (readOnlyProfile db) (.writeDb conn db offset bytes) =
      ITree.ret (.error (.denied .writeForbidden)) := by
  simp [guardedCall, checkEvent, readOnlyProfile]

@[simp] theorem guardedCall_attach_denied (db target : DbId) (conn : ConnHandle)
    (schemaName : String) :
    guardedCall (readOnlyProfile db) (.attachDb conn target schemaName) =
      ITree.ret (.error (.denied .attachForbidden)) := by
  simp [guardedCall, checkEvent, readOnlyProfile]

@[simp] theorem guardedCall_extension_denied (db : DbId) (conn : ConnHandle)
    (path : String) :
    guardedCall (readOnlyProfile db) (.loadExtension conn path) =
      ITree.ret (.error (.denied .extensionForbidden)) := by
  simp [guardedCall, checkEvent, readOnlyProfile]

@[simp] theorem guardedCall_hostEffect_denied (db : DbId) (kind : HostEffectKind) :
    guardedCall (readOnlyProfile db) (.hostEffect kind) =
      ITree.ret (.error (.denied .hostEffectForbidden)) := by
  simp [guardedCall, checkEvent, readOnlyProfile]

theorem guardedDeniedWriteSession_safe (db : DbId) (offset : Nat) (bytes : List UInt8) :
    TreeSafe (readOnlyProfile db) (guardedDeniedWriteSession db offset bytes) :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.guardedDeniedWriteSession_safe db offset bytes

theorem guardedDeniedWriteSession_returnsTo_preserves_protected {S P : Type}
    {step : ApiHandler S} {protectedState : S → P}
    (db : DbId) (offset : Nat) (bytes : List UInt8)
    (hframe : FrameContract (readOnlyProfile db) step protectedState)
    {s s' : S} {res : Except ApiError Unit}
    (hret : ITree.ReturnsTo step s (guardedDeniedWriteSession db offset bytes) s' res) :
    protectedState s' = protectedState s :=
  treeSafe_returnsTo_preserves_protected hframe
    (guardedDeniedWriteSession_safe db offset bytes) hret

/-! ## Negative witnesses: forbidden operations are representable and rejected by `TreeSafe` -/

theorem unsafeWriteProgram_not_safe (conn : ConnHandle) (db : DbId)
    (offset : Nat) (bytes : List UInt8) :
    ¬ TreeSafe (readOnlyProfile db) (unsafeWriteProgram conn db offset bytes) := by
  intro hsafe
  exact eventAllowed_readOnly_writeDb db db conn offset bytes
    (hsafe (.request (.writeDb conn db offset bytes)) (ITree.hasTrace_vis_request _ _))

theorem unsafeAttachProgram_not_safe (conn : ConnHandle) (db target : DbId)
    (schemaName : String) :
    ¬ TreeSafe (readOnlyProfile db) (unsafeAttachProgram conn target schemaName) := by
  intro hsafe
  exact eventAllowed_readOnly_attachDb db target conn schemaName
    (hsafe (.request (.attachDb conn target schemaName)) (ITree.hasTrace_vis_request _ _))

theorem unsafeLoadExtensionProgram_not_safe (conn : ConnHandle) (db : DbId)
    (path : String) :
    ¬ TreeSafe (readOnlyProfile db) (unsafeLoadExtensionProgram conn path) := by
  intro hsafe
  exact eventAllowed_readOnly_loadExtension db conn path
    (hsafe (.request (.loadExtension conn path)) (ITree.hasTrace_vis_request _ _))

theorem unsafeHostEffectProgram_not_safe (db : DbId) (kind : HostEffectKind) :
    ¬ TreeSafe (readOnlyProfile db) (unsafeHostEffectProgram kind) := by
  intro hsafe
  exact eventAllowed_readOnly_hostEffect db kind
    (hsafe (.request (.hostEffect kind)) (ITree.hasTrace_vis_request _ _))

theorem unsafeReadWriteOpenProgram_not_safe (db : DbId) :
    ¬ TreeSafe (readOnlyProfile db) (unsafeReadWriteOpenProgram db) := by
  intro hsafe
  exact eventAllowed_readOnly_openDb_readWrite db db
    (hsafe (.request (.openDb db .readWrite)) (ITree.hasTrace_vis_request _ _))

theorem unsafeWrongDbOpenProgram_not_safe {db otherDb : DbId} (hne : otherDb ≠ db) :
    ¬ TreeSafe (readOnlyProfile db) (unsafeWrongDbOpenProgram otherDb) := by
  intro hsafe
  exact hne ((eventAllowed_readOnly_openDb_readOnly db otherDb).mp
    (hsafe (.request (.openDb otherDb .readOnly)) (ITree.hasTrace_vis_request _ _)))

/-! ## Reference handler witness and frame-contract honesty witness -/

/-- The concrete single-connection `referenceHandler` satisfies `FrameContract`
for `readOnlyProfile db` (even though it allows `writeDb` to mutate
`protectedDb` when unguarded). -/
theorem referenceHandler_frameContract (db : DbId) :
    FrameContract (readOnlyProfile db) referenceHandler ReferenceState.protectedDb :=
  Silmaril.Proofs.Semantics.SQLite.Isolation.Api.referenceHandler_frameContract db

/-- Honesty witness: `TreeSafe` alone does not prevent a dishonest handler from
mutating state; `FrameContract` is genuinely required for state preservation. -/
theorem dishonestHandler_mutates_despite_treeSafe (db : DbId) :
    TreeSafe (readOnlyProfile db) (rawCall (.openDb db .readOnly)) ∧
    ITree.ReturnsTo dishonestHandler 0 (rawCall (.openDb db .readOnly)) 1 (.ok ⟨0⟩) ∧
    (1 : Nat) ≠ 0 :=
  ⟨treeSafe_rawCall ((eventAllowed_readOnly_openDb_readOnly db db).mpr rfl),
   ITree.ReturnsTo.exchange ⟨rfl, rfl⟩
     (ITree.ReturnsTo.ret 1 (Except.ok (ConnHandle.mk 0) : Except ApiError ConnHandle)),
   Nat.one_ne_zero⟩

end Silmaril.SQLite.Isolation.Api
