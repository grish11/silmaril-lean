module

public import Silmaril.Formats.Git.Arena.Equality.Defs
public import Silmaril.Formats.Git.Arena.Collision.Thms
public import Silmaril.Formats.Git.Arena.Thms
import Silmaril.Proofs.Formats.Git.Arena.Equality

public section

namespace Silmaril.Formats.Git.Arena.Equality

variable {Name Payload Value : Type} {limit : Nat}
variable [DecidableEq Name] [DecidableEq Payload]
variable {snapshot : Snapshot limit Name Payload} {request : Request limit Name} {oid : Oid}
variable {requests : List (Request limit Name)}

theorem Snapshot.check_sound (coherent : snapshot.arena.Coherent snapshot.profile)
    (checked : snapshot.check request = .ok ()) :
    ∃ payload, snapshot.payloadAt request.left = some payload ∧ snapshot.payloadAt request.right = some payload :=
  Proofs.Formats.Git.Arena.Equality.check_sound coherent checked

omit [DecidableEq Name] [DecidableEq Payload] in
/-- Same-lane deterministic canonical derivations justify disequality without
injectivity, even if an unchecked caller attached the same Git label. -/
theorem Snapshot.derived_different {lane : CasLane} {left right : Payload} {first last : Name}
    (derivedLeft : snapshot.profile.derive (.cas lane) left = some (.cas lane first))
    (derivedRight : snapshot.profile.derive (.cas lane) right = some (.cas lane last)) (different : first ≠ last) :
    left ≠ right := by
  rintro rfl
  exact different (by simpa using derivedLeft.symm.trans derivedRight)

theorem Snapshot.reject_different_cas {lane : CasLane} {left right : Payload} {first last : Name}
    (foundLeft : snapshot.payloadAt request.left = some left) (foundRight : snapshot.payloadAt request.right = some right)
    (derivedLeft : snapshot.profile.derive (.cas lane) left = some (.cas lane first))
    (derivedRight : snapshot.profile.derive (.cas lane) right = some (.cas lane last)) (different : first ≠ last) :
    snapshot.check request ≠ .ok () :=
  Proofs.Formats.Git.Arena.Equality.different_cas_reject foundLeft foundRight derivedLeft derivedRight different

theorem Snapshot.check_oid_hit (checked : snapshot.check request = .ok ()) (uses : request.evidence.oid? = some oid) :
    ∃ bytes, snapshot.git.query oid = .hit bytes := Proofs.Formats.Git.Arena.Equality.check_oid_hit checked uses

theorem Snapshot.check_oid_verified {verifier : Collision.Verifier} (valid : snapshot.git.Valid verifier)
    (checked : snapshot.check request = .ok ()) (uses : request.evidence.oid? = some oid) :
    ∃ bytes, snapshot.git.query oid = .hit bytes ∧ verifier.verify oid bytes = .verified := by
  obtain ⟨bytes, hit⟩ := snapshot.check_oid_hit checked uses
  exact ⟨bytes, hit, snapshot.git.query_hit_verified valid hit⟩

theorem Snapshot.mem_replay : request ∈ snapshot.replay requests ↔ request ∈ requests ∧ snapshot.check request = .ok () :=
  Proofs.Formats.Git.Arena.Equality.mem_replay

theorem Snapshot.related_content {left right : Fin limit} (coherent : snapshot.arena.Coherent snapshot.profile)
    (related : Related (snapshot.replay requests) left right) : snapshot.payloadAt left = snapshot.payloadAt right :=
  Proofs.Formats.Git.Arena.Equality.related_sound coherent related

theorem Snapshot.related_typed {left right : Fin limit} (coherent : snapshot.arena.Coherent snapshot.profile)
    (related : Related (snapshot.replay requests) left right)
    (codec : Dasl.Encode.PartialCodec Value ByteArray) (encode : Payload → Option ByteArray) :
    snapshot.typedAt codec encode left = snapshot.typedAt codec encode right :=
  congrArg (fun payload => payload.bind fun content => (encode content).bind codec.decode?)
    (snapshot.related_content coherent related)

/-- Read the bytes of an actually observed name at an equivalent resident,
without asserting that the destination key claims the name. -/
theorem Snapshot.related_readWire {left right : Fin limit} {id : Arena.Id Name} {payload : Payload} {bytes : ByteArray}
    (coherent : snapshot.arena.Coherent snapshot.profile) (related : Related (snapshot.replay requests) left right)
    (resident : snapshot.payloadAt left = some payload) (named : snapshot.arena.observed id payload)
    (found : snapshot.arena.readWire snapshot.profile id = .found bytes) :
    snapshot.payloadAt right = some payload ∧ snapshot.profile.wire id payload = some bytes := by
  obtain ⟨original, seen, wire⟩ := State.readWire_found found
  exact ⟨(snapshot.related_content coherent related).symm.trans resident, State.observed_binding coherent seen named ▸ wire⟩

theorem Snapshot.related_reject_different_cas {left right : Fin limit} {lane : CasLane}
    {leftPayload rightPayload : Payload} {first last : Name}
    (coherent : snapshot.arena.Coherent snapshot.profile)
    (foundLeft : snapshot.payloadAt left = some leftPayload) (foundRight : snapshot.payloadAt right = some rightPayload)
    (derivedLeft : snapshot.profile.derive (.cas lane) leftPayload = some (.cas lane first))
    (derivedRight : snapshot.profile.derive (.cas lane) rightPayload = some (.cas lane last)) (different : first ≠ last) :
    ¬ Related (snapshot.replay requests) left right := by
  intro related
  have same := foundLeft.symm.trans ((snapshot.related_content coherent related).trans foundRight)
  exact snapshot.derived_different derivedLeft derivedRight different (Option.some.inj same)

/-- This monotonicity pins the *whole* admission snapshot. It makes no claim
across changed trust, arena data, collision information or naming profiles. -/
theorem Snapshot.related_monotone {later : List (Request limit Name)} {left right : Fin limit}
    (included : requests ⊆ later) (related : Related (snapshot.replay requests) left right) :
    Related (snapshot.replay later) left right := Proofs.Formats.Git.Arena.Equality.related_monotone included related

theorem Snapshot.check_blocked (uses : request.evidence.oid? = some oid) (blocked : snapshot.blocked oid = true) :
    snapshot.check request = .error .oidBlocked := by simp [Snapshot.check, uses, blocked]

theorem Snapshot.replay_excludes_blocked (uses : request.evidence.oid? = some oid) (blocked : snapshot.blocked oid = true) :
    request ∉ snapshot.replay requests := by
  intro member
  have admitted := (Snapshot.mem_replay.mp member).2
  simp [snapshot.check_blocked uses blocked] at admitted

theorem Snapshot.replay_excludes_nonunique (uses : request.evidence.oid? = some oid)
    (nonunique : ∀ bytes, snapshot.git.query oid ≠ .hit bytes) : request ∉ snapshot.replay requests := by
  intro member
  obtain ⟨bytes, hit⟩ := snapshot.check_oid_hit (Snapshot.mem_replay.mp member).2 uses
  exact nonunique bytes hit

theorem Snapshot.replay_after_delivery {outcome : Collision.Outcome} (collision : outcome.isCollision = true)
    (uses : request.evidence.oid? = some oid) : request ∉ (snapshot.deliver oid outcome).replay requests :=
  Snapshot.replay_excludes_blocked uses (Collision.Disputes.record_blocked collision)

theorem Snapshot.replay_after_revocation (uses : request.evidence.oid? = some oid) :
    request ∉ (snapshot.revoke oid).replay requests :=
  Snapshot.replay_excludes_blocked uses (by simp [Snapshot.revoke])

/-- Current OID observations, revocations and authorities do not affect
independent content or canonical CAS requests. -/
theorem Snapshot.check_nonOid_frame (independent : request.evidence.oid? = none)
    (git : Collision.Index) (blocked : Collision.Disputes) (authority : Option (Sha256Authority Payload)) :
    ({ snapshot with git, blocked, authority } : Snapshot limit Name Payload).check request = snapshot.check request := by
  cases tag : request.evidence <;> simp [tag, Evidence.oid?] at independent
  all_goals simp [Snapshot.check, Snapshot.checkEvidence, Snapshot.payloadAt, Snapshot.casDifferent,
    Snapshot.claimsAt, tag, Evidence.oid?]
  rfl

theorem Snapshot.readRaw_delivery (outcome : Collision.Outcome) (name : Name) :
    (snapshot.deliver oid outcome).readRaw name = snapshot.readRaw name := rfl

theorem Snapshot.readRaw_revocation (name : Name) : (snapshot.revoke oid).readRaw name = snapshot.readRaw name := rfl

end Silmaril.Formats.Git.Arena.Equality
