module

public import Silmaril.Formats.Git.Arena.Collision.Defs
import Silmaril.Proofs.Formats.Git.Arena.Collision

public section

namespace Silmaril.Formats.Git.Arena.Collision

theorem Verifier.verified_iff {verifier : Verifier} {oid : Oid} {bytes : ByteArray} :
    verifier.verify oid bytes = .verified ↔ verifier.admits oid.algorithm bytes = true ∧ ∃ digest,
      verifier.digest oid.algorithm bytes = some digest ∧ Oid.ofBytes oid.algorithm digest = oid :=
  Proofs.Formats.Git.Arena.Collision.verified_iff

variable {verifier : Verifier} {policies other : Policies} {index : Index} {oid : Oid} {input : Input}
variable {bytes incumbent : ByteArray} {alternatives : List ByteArray}

theorem Index.empty_valid : Index.empty.Valid verifier := by
  intro oid
  simp [Index.empty, Bucket.candidates]

theorem Index.step_frame {key : Oid} (different : key ≠ oid) :
    (index.step verifier policies oid input).2 key = index key :=
  Proofs.Formats.Git.Arena.Collision.step_frame different

theorem Index.step_valid (valid : index.Valid verifier) : (index.step verifier policies oid input).2.Valid verifier :=
  Proofs.Formats.Git.Arena.Collision.valid_step valid

/-- No event can lose a candidate or replace the first verified preimage. -/
theorem Index.step_extends : index.Extends (index.step verifier policies oid input).2 :=
  Proofs.Formats.Git.Arena.Collision.step_extends

theorem Index.step_missing : index.step verifier policies oid .missing = (.missing, index) := rfl

theorem Index.step_claim (vacant : index oid = .empty) :
    index.step verifier policies oid .claim = (.claimed, index.put oid .claim) := by
  simp [Index.step, Bucket.edit, vacant]

theorem Index.step_failed_preimage (failed : verifier.verify oid bytes ≠ .verified) :
    index.step verifier policies oid (.preimage bytes) =
      (match verifier.verify oid bytes with
        | .verified => .inserted
        | .malformed => .malformed
        | .unavailable => .unavailable
        | .mismatch => .mismatch, index) :=
  Proofs.Formats.Git.Arena.Collision.failed_preimage failed

/-- Reobserving any exact candidate (including a retained alternative) is a no-op. -/
theorem Index.step_duplicate (verified : verifier.verify oid bytes = .verified)
    (known : bytes ∈ (index oid).candidates) :
    index.step verifier policies oid (.preimage bytes) = (.duplicate, index) :=
  Proofs.Formats.Git.Arena.Collision.verified_duplicate verified known

theorem Index.step_strict_collision (policy : policies oid.algorithm = .strict)
    (present : index oid = .verified incumbent alternatives)
    (verified : verifier.verify oid bytes = .verified) (fresh : bytes ∉ incumbent :: alternatives) :
    index.step verifier policies oid (.preimage bytes) = (.rejectedCollision, index) :=
  Proofs.Formats.Git.Arena.Collision.strict_collision policy present verified fresh

theorem Index.step_retain_collision (policy : policies oid.algorithm = .retain)
    (present : index oid = .verified incumbent alternatives)
    (verified : verifier.verify oid bytes = .verified) (fresh : bytes ∉ incumbent :: alternatives) :
    index.step verifier policies oid (.preimage bytes) =
      (.retainedCollision, index.put oid (.verified incumbent (bytes :: alternatives))) :=
  Proofs.Formats.Git.Arena.Collision.retain_collision policy present verified fresh

theorem Index.query_retain_collision (policy : policies oid.algorithm = .retain)
    (present : index oid = .verified incumbent alternatives)
    (verified : verifier.verify oid bytes = .verified) (fresh : bytes ∉ incumbent :: alternatives) :
    (index.step verifier policies oid (.preimage bytes)).2.query oid = .ambiguous incumbent bytes alternatives :=
  Proofs.Formats.Git.Arena.Collision.retain_query policy present verified fresh

/-- From the same singleton bucket, a verified distinct preimage leaves the
strict index intact but takes away the retaining index's unique hit. -/
theorem Index.first_collision (strict : policies oid.algorithm = .strict) (retain : other oid.algorithm = .retain)
    (present : index oid = .verified incumbent []) (verified : verifier.verify oid bytes = .verified)
    (different : bytes ≠ incumbent) :
    index.step verifier policies oid (.preimage bytes) = (.rejectedCollision, index) ∧
      (index.step verifier other oid (.preimage bytes)).2.query oid = .ambiguous incumbent bytes [] := by
  have fresh : bytes ∉ [incumbent] := by simpa using different
  exact ⟨step_strict_collision strict present verified fresh, query_retain_collision retain present verified fresh⟩

theorem Index.query_hit_verified (valid : index.Valid verifier) (hit : index.query oid = .hit bytes) :
    verifier.verify oid bytes = .verified :=
  Proofs.Formats.Git.Arena.Collision.hit_verified valid hit

theorem Index.no_hit_after_dispute {updated : Index} {left right : ByteArray}
    (extended : index.Extends updated) (first : left ∈ (index oid).candidates)
    (second : right ∈ (index oid).candidates) (different : left ≠ right) : updated.query oid ≠ .hit bytes :=
  Proofs.Formats.Git.Arena.Collision.no_hit_after_dispute extended first second different

theorem Index.run_valid {events : List Event} (valid : index.Valid verifier) :
    (index.run verifier policies events).2.Valid verifier :=
  Proofs.Formats.Git.Arena.Collision.run_valid valid

/-- Stronger than read equivalence: policy configurations produce identical
outcomes and final indices on each collision-free prefix. -/
theorem Index.run_agree {events : List Event} (safe : index.CollisionFree verifier events) :
    index.run verifier policies events = index.run verifier other events :=
  Proofs.Formats.Git.Arena.Collision.run_agree safe

variable {Name Payload : Type} {limit : Nat} {store : Store limit Name Payload}

theorem Store.step_cas : (store.step verifier policies oid input).2.cas = store.cas := rfl

theorem Store.step_readRaw [DecidableEq Name] [DecidableEq Payload] (profile : Arena.Profile Name Payload)
    (name : Name) : (store.step verifier policies oid input).2.readRaw profile name = store.readRaw profile name := rfl

theorem Store.step_strict_collision (policy : policies oid.algorithm = .strict)
    (present : store.git oid = .verified incumbent alternatives)
    (verified : verifier.verify oid bytes = .verified) (fresh : bytes ∉ incumbent :: alternatives) :
    store.step verifier policies oid (.preimage bytes) = (.rejectedCollision, store) := by
  unfold Store.step
  rw [Index.step_strict_collision policy present verified fresh]

theorem Disputes.record_blocked {blocked : Disputes} {outcome : Outcome} (collision : outcome.isCollision = true) :
    blocked.record oid outcome oid = true := by simp [Disputes.record, collision]

theorem Disputes.record_preserves {blocked : Disputes} {outcome : Outcome} {key : Oid}
    (prior : blocked key = true) : blocked.record oid outcome key = true := by simp [Disputes.record, prior]

variable {Value : Type} {blocked : Disputes} {encode : Value → Option ByteArray} {left right : Value}

theorem Index.canSeed_iff :
    index.canSeed blocked encode oid left right = true ↔ index.Seed blocked encode oid left right :=
  Proofs.Formats.Git.Arena.Collision.canSeed_iff

theorem Index.seed_refuse_blocked (disputed : blocked oid = true) : ¬ index.Seed blocked encode oid left right :=
  fun seed => Bool.noConfusion (disputed.symm.trans seed.1)

theorem Index.seed_refuse_nonhit (nonhit : ∀ bytes, index.query oid ≠ .hit bytes) :
    ¬ index.Seed blocked encode oid left right :=
  fun ⟨_, bytes, hit, _, _⟩ => nonhit bytes hit

theorem Index.seed_verified (valid : index.Valid verifier) (seed : index.Seed blocked encode oid left right) :
    ∃ bytes, verifier.verify oid bytes = .verified ∧ encode left = some bytes ∧ encode right = some bytes := by
  obtain ⟨_, bytes, hit, first, second⟩ := seed
  exact ⟨bytes, query_hit_verified valid hit, first, second⟩

/-- Only actual matching endpoint bytes plus a recovering codec imply
equality. No injectivity assumption on the digest oracle is used. -/
theorem Index.seed_sound {decode : ByteArray → Option Value}
    (recover : ∀ value bytes, encode value = some bytes → decode bytes = some value)
    (seed : index.Seed blocked encode oid left right) : left = right := by
  obtain ⟨_, bytes, _, first, second⟩ := seed
  exact Option.some.inj ((recover left bytes first).symm.trans (recover right bytes second))

end Silmaril.Formats.Git.Arena.Collision
