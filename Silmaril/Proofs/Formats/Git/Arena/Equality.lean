module

public import Silmaril.Formats.Git.Arena.Equality.Defs
public import Silmaril.Formats.Git.Arena.Collision.Thms
public import Silmaril.Formats.Git.Arena.Thms

public section

namespace Silmaril.Proofs.Formats.Git.Arena.Equality

open Silmaril.Formats.Git
open Silmaril.Formats.Git.Arena
open Silmaril.Formats.Git.Arena.Equality

variable {Name Payload : Type} {limit : Nat}
variable {snapshot : Snapshot limit Name Payload} {request : Request limit Name}
variable {requests : List (Request limit Name)} {oid : Oid}

private theorem at_observed {key : Fin limit} {id : Arena.Id Name} {payload : Payload}
    (atKey : snapshot.payloadAt key = some payload) (named : id ∈ snapshot.claimsAt key) :
    snapshot.arena.observed id payload := by
  cases atCell : snapshot.arena key with
  | none => simp [Snapshot.payloadAt, atCell] at atKey
  | some cell =>
    simp [Snapshot.payloadAt, atCell] at atKey
    simp only [Snapshot.claimsAt, atCell, Option.map_some, Option.getD_some] at named
    exact ⟨key, cell, atCell, named, atKey⟩

variable [DecidableEq Name] [DecidableEq Payload]

private theorem evidence_sound (coherent : snapshot.arena.Coherent snapshot.profile)
    {left right : Payload} (first : snapshot.payloadAt request.left = some left)
    (second : snapshot.payloadAt request.right = some right)
    (checked : snapshot.checkEvidence request left right = .ok ()) : left = right := by
  cases tag : request.evidence with
  | content =>
    by_contra different
    simp [Snapshot.checkEvidence, tag, different] at checked
  | canonicalCas lane name =>
    simp only [Snapshot.checkEvidence, tag] at checked
    split at checked
    · rename_i named
      exact State.observed_binding coherent (at_observed first named.1) (at_observed second named.2.1)
    · contradiction
  | nativeBytes oid =>
    simp only [Snapshot.checkEvidence, tag] at checked
    split at checked
    · rename_i enabled
      exact Collision.Index.seed_sound (snapshot.nativeCodec oid.algorithm).recovers
        (Collision.Index.canSeed_iff.mp enabled)
    · contradiction
  | trustedGit oid =>
    cases oid with
    | sha1 name => simp [Snapshot.checkEvidence, tag] at checked
    | sha256 name =>
      cases trust : snapshot.authority with
      | none => simp [Snapshot.checkEvidence, tag, trust] at checked
      | some authority =>
        cases hit : snapshot.git.query (.sha256 name) <;> simp [Snapshot.checkEvidence, tag, trust, hit] at checked
        exact authority.binds checked.1 checked.2

private theorem checked_resident (checked : snapshot.check request = .ok ()) :
    ∃ left right, snapshot.payloadAt request.left = some left ∧ snapshot.payloadAt request.right = some right ∧
      snapshot.checkEvidence request left right = .ok () := by
  unfold Snapshot.check at checked
  split at checked
  · contradiction
  cases first : snapshot.payloadAt request.left with
  | none => simp [first] at checked
  | some left =>
    cases second : snapshot.payloadAt request.right with
    | none => simp [first, second] at checked
    | some right =>
      simp only [first, second] at checked
      split at checked
      · contradiction
      split at checked
      · contradiction
      exact ⟨left, right, rfl, rfl, checked⟩

theorem check_sound (coherent : snapshot.arena.Coherent snapshot.profile)
    (checked : snapshot.check request = .ok ()) :
    ∃ payload, snapshot.payloadAt request.left = some payload ∧ snapshot.payloadAt request.right = some payload := by
  obtain ⟨left, right, first, second, checkedEvidence⟩ := checked_resident checked
  have same := evidence_sound coherent first second checkedEvidence
  exact ⟨left, first, same.symm ▸ second⟩

theorem check_oid_hit (checked : snapshot.check request = .ok ()) (uses : request.evidence.oid? = some oid) :
    ∃ bytes, snapshot.git.query oid = .hit bytes := by
  obtain ⟨left, right, _, _, checkedEvidence⟩ := checked_resident checked
  cases tag : request.evidence with
  | content | canonicalCas => simp [tag, Evidence.oid?] at uses
  | nativeBytes claimed =>
    have same : claimed = oid := by simpa [tag, Evidence.oid?] using uses
    subst claimed
    simp only [Snapshot.checkEvidence, tag] at checkedEvidence
    split at checkedEvidence
    · rename_i accepted
      obtain ⟨_, bytes, hit, _, _⟩ := Collision.Index.canSeed_iff.mp accepted
      exact ⟨bytes, hit⟩
    · contradiction
  | trustedGit claimed =>
    have same : claimed = oid := by simpa [tag, Evidence.oid?] using uses
    subst claimed
    cases oid with
    | sha1 name => simp [Snapshot.checkEvidence, tag] at checkedEvidence
    | sha256 name =>
      cases trust : snapshot.authority with
      | none => simp [Snapshot.checkEvidence, tag, trust] at checkedEvidence
      | some authority =>
        cases hit : snapshot.git.query (.sha256 name) <;> simp [Snapshot.checkEvidence, tag, trust, hit] at checkedEvidence
        exact ⟨_, rfl⟩

theorem different_cas_reject {lane : CasLane} {left right : Payload} {first last : Name}
    (foundLeft : snapshot.payloadAt request.left = some left) (foundRight : snapshot.payloadAt request.right = some right)
    (derivedLeft : snapshot.profile.derive (.cas lane) left = some (.cas lane first))
    (derivedRight : snapshot.profile.derive (.cas lane) right = some (.cas lane last)) (different : first ≠ last) :
    snapshot.check request ≠ .ok () := by
  have compare : snapshot.casDifferent lane left right = true := by
    simp [Snapshot.casDifferent, derivedLeft, derivedRight, different]
  by_cases blocked : request.evidence.oid?.any snapshot.blocked = true
  · simp [Snapshot.check, blocked]
  cases lane with
  | raw => simp [Snapshot.check, blocked, foundLeft, foundRight, compare]
  | object =>
    by_cases raw : snapshot.casDifferent .raw left right = true <;>
      simp [Snapshot.check, blocked, foundLeft, foundRight, raw, compare]

theorem mem_replay : request ∈ snapshot.replay requests ↔ request ∈ requests ∧ snapshot.check request = .ok () := by
  rw [Snapshot.replay, List.mem_filter]
  cases checked : snapshot.check request with
  | ok value => cases value; simp [Except.isOk, Except.toBool]
  | error fault => simp [Except.isOk, Except.toBool]

theorem related_sound {left right : Fin limit} (coherent : snapshot.arena.Coherent snapshot.profile)
    (related : Related (snapshot.replay requests) left right) : snapshot.payloadAt left = snapshot.payloadAt right := by
  induction related with
  | refl => rfl
  | edge member =>
    obtain ⟨_, leftHit, rightHit⟩ := check_sound coherent (mem_replay.mp member).2
    exact leftHit.trans rightHit.symm
  | symm _ same => exact same.symm
  | trans _ _ first second => exact first.trans second

theorem related_monotone {later : List (Request limit Name)} {left right : Fin limit}
    (included : requests ⊆ later) (related : Related (snapshot.replay requests) left right) :
    Related (snapshot.replay later) left right := by
  induction related with
  | refl => exact .refl _
  | edge member =>
    obtain ⟨requested, checked⟩ := mem_replay.mp member
    exact .edge (mem_replay.mpr ⟨included requested, checked⟩)
  | symm _ later => exact .symm later
  | trans _ _ first second => exact .trans first second

end Silmaril.Proofs.Formats.Git.Arena.Equality
