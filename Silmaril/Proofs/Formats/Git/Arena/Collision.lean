module

public import Silmaril.Formats.Git.Arena.Collision.Defs

public section

namespace Silmaril.Proofs.Formats.Git.Arena.Collision

open Silmaril.Formats.Git.Arena
open Silmaril.Formats.Git.Arena.Collision

variable {verifier : Verifier} {policies : Policies} {index : Index} {oid : Oid} {input : Input}
variable {bytes incumbent : ByteArray} {alternatives : List ByteArray}

theorem verified_iff : verifier.verify oid bytes = .verified ↔
    verifier.admits oid.algorithm bytes = true ∧ ∃ digest,
      verifier.digest oid.algorithm bytes = some digest ∧ Oid.ofBytes oid.algorithm digest = oid := by
  unfold Verifier.verify
  split <;> rename_i admitted
  · cases eq : verifier.digest oid.algorithm bytes with
    | none => simp
    | some digest => simp [admitted, ite_eq_left_iff]
  · simp [admitted]

theorem step_at : (index.step verifier policies oid input).2 oid =
    ((index oid).edit verifier (policies oid.algorithm) oid input).2.getD (index oid) := by
  cases edit : (index oid).edit verifier (policies oid.algorithm) oid input with
  | mk outcome update => cases update <;> simp [Index.step, edit, Index.put]

theorem step_frame {key : Oid} (different : key ≠ oid) :
    (index.step verifier policies oid input).2 key = index key := by
  cases edit : (index oid).edit verifier (policies oid.algorithm) oid input with
  | mk outcome update => cases update <;> simp [Index.step, edit, Index.put, different]

theorem verified_duplicate (verified : verifier.verify oid bytes = .verified)
    (known : bytes ∈ (index oid).candidates) :
    index.step verifier policies oid (.preimage bytes) = (.duplicate, index) := by
  simp [Index.step, Bucket.edit, verified, Bucket.admit, known]

theorem strict_collision (policy : policies oid.algorithm = .strict)
    (present : index oid = .verified incumbent alternatives)
    (verified : verifier.verify oid bytes = .verified) (fresh : bytes ∉ incumbent :: alternatives) :
    index.step verifier policies oid (.preimage bytes) = (.rejectedCollision, index) := by
  simp [Index.step, present, Bucket.edit, verified, Bucket.admit, Bucket.candidates, fresh, policy]

theorem retain_collision (policy : policies oid.algorithm = .retain)
    (present : index oid = .verified incumbent alternatives)
    (verified : verifier.verify oid bytes = .verified) (fresh : bytes ∉ incumbent :: alternatives) :
    index.step verifier policies oid (.preimage bytes) =
      (.retainedCollision, index.put oid (.verified incumbent (bytes :: alternatives))) := by
  simp [Index.step, present, Bucket.edit, verified, Bucket.admit, Bucket.candidates, fresh, policy]

theorem failed_preimage (failed : verifier.verify oid bytes ≠ .verified) :
    index.step verifier policies oid (.preimage bytes) =
      (match verifier.verify oid bytes with
        | .verified => .inserted
        | .malformed => .malformed
        | .unavailable => .unavailable
        | .mismatch => .mismatch, index) := by
  cases verdict : verifier.verify oid bytes <;> simp_all [Index.step, Bucket.edit]

private theorem local_update {bucket : Bucket} {policy : Policy} {updated : Bucket}
    (edit : (bucket.edit verifier policy oid input).2 = some updated) :
    (bucket = .empty ∧ updated = .claim) ∨
    ∃ bytes, verifier.verify oid bytes = .verified ∧ bytes ∉ bucket.candidates ∧
      (updated = .verified bytes [] ∧ bucket.incumbent = none ∨
        ∃ incumbent alternatives, bucket = .verified incumbent alternatives ∧
          updated = .verified incumbent (bytes :: alternatives)) := by
  cases input with
  | missing => simp [Bucket.edit] at edit
  | claim => cases bucket <;> simp_all [Bucket.edit]
  | preimage bytes =>
    cases verification : verifier.verify oid bytes <;> simp [Bucket.edit, verification] at edit
    by_cases known : bytes ∈ bucket.candidates
    · simp [Bucket.admit, known] at edit
    refine Or.inr ⟨bytes, verification, known, ?_⟩
    cases bucket <;> cases policy <;> simp_all [Bucket.admit, Bucket.incumbent]

theorem valid_step (valid : index.Valid verifier) : (index.step verifier policies oid input).2.Valid verifier := by
  intro key
  by_cases same : key = oid
  · subst key
    rw [step_at]
    cases update : ((index oid).edit verifier (policies oid.algorithm) oid input).2 with
    | none => exact valid oid
    | some next =>
      change next.candidates.Nodup ∧ ∀ candidate ∈ next.candidates, _
      rcases local_update update with ⟨_, rfl⟩ | ⟨bytes, verified, fresh, changed⟩
      · simp [Bucket.candidates]
      rcases changed with ⟨rfl, _⟩ | ⟨incumbent, alternatives, old, rfl⟩
      · simp [Bucket.candidates, verified]
      have previous := valid oid
      rw [old] at previous fresh
      simp only [Bucket.candidates] at fresh previous ⊢
      rcases previous with ⟨nodup, verifiedOld⟩
      rw [List.nodup_cons] at nodup ⊢
      simp only [List.mem_cons, not_or] at fresh
      refine ⟨⟨?_, List.nodup_cons.mpr ⟨fresh.2, nodup.2⟩⟩, ?_⟩
      · simp [Ne.symm fresh.1, nodup.1]
      · intro candidate member
        simp only [List.mem_cons] at member
        rcases member with same | same | known
        · exact verifiedOld candidate (by simp [same])
        · simpa [same] using verified
        · exact verifiedOld candidate (by simp [known])
  · rw [step_frame same]
    exact valid key

theorem step_extends : index.Extends (index.step verifier policies oid input).2 := by
  intro key
  by_cases same : key = oid
  · subst key
    rw [step_at]
    cases update : ((index oid).edit verifier (policies oid.algorithm) oid input).2 with
    | none => exact ⟨fun _ member => member, fun _ member => member⟩
    | some next =>
      change (∀ bytes ∈ (index oid).incumbent, next.incumbent = some bytes) ∧
        (index oid).candidates ⊆ next.candidates
      rcases local_update update with ⟨prior, rfl⟩ | ⟨bytes, _, _, changed⟩
      · simp [prior, Bucket.incumbent, Bucket.candidates]
      rcases changed with ⟨rfl, noneBefore⟩ | ⟨incumbent, alternatives, old, rfl⟩
      · cases prior : index oid <;> simp_all [Bucket.incumbent, Bucket.candidates]
      · simp only [old, Bucket.incumbent, Bucket.candidates]
        exact ⟨fun _ member => member, by
          intro candidate member
          simp only [List.mem_cons] at member ⊢
          exact member.imp_right Or.inr⟩
  · rw [step_frame same]
    exact ⟨fun _ member => member, fun _ member => member⟩

theorem step_agree {other : Policies} (safe : index.Safe verifier oid input) :
    index.step verifier policies oid input = index.step verifier other oid input := by
  cases input with
  | claim => cases eq : index oid <;> simp [Index.step, Bucket.edit, eq]
  | missing => rfl
  | preimage bytes =>
    cases verdict : verifier.verify oid bytes <;> simp [Index.step, Bucket.edit, verdict]
    cases eq : index oid with
    | empty => simp [Bucket.admit, Bucket.candidates]
    | claim => simp [Bucket.admit, Bucket.candidates]
    | verified first rest =>
      have same := safe verdict first (by simp [eq, Bucket.incumbent])
      simp [Bucket.admit, Bucket.candidates, same]

theorem run_agree {events : List Event} {other : Policies}
    (safe : index.CollisionFree verifier events) :
    index.run verifier policies events = index.run verifier other events := by
  induction events generalizing index with
  | nil => rfl
  | cons event rest ih =>
    obtain ⟨oid, input⟩ := event
    obtain ⟨safeHead, safeTail⟩ := safe
    simp only [Index.run, step_agree (other := fun _ => .retain) safeHead, ih safeTail]

theorem run_valid {events : List Event} (valid : index.Valid verifier) :
    (index.run verifier policies events).2.Valid verifier := by
  induction events generalizing index with
  | nil => exact valid
  | cons event rest ih =>
    obtain ⟨oid, input⟩ := event
    exact ih (valid_step (oid := oid) (input := input) valid)

theorem hit_eq {candidate : ByteArray} (hit : index.query oid = .hit bytes)
    (member : candidate ∈ (index oid).candidates) : candidate = bytes := by
  cases cell : index oid with
  | empty | claim => simp [Index.query, cell, Bucket.query] at hit
  | verified first rest => cases rest <;> simp_all [Index.query, Bucket.query, Bucket.candidates]

theorem hit_verified (valid : index.Valid verifier) (hit : index.query oid = .hit bytes) :
    verifier.verify oid bytes = .verified := by
  apply (valid oid).2 bytes
  cases cell : index oid with
  | empty | claim => simp [Index.query, cell, Bucket.query] at hit
  | verified first rest => cases rest <;> simp_all [Index.query, Bucket.query, Bucket.candidates]

theorem retain_query (policy : policies oid.algorithm = .retain)
    (present : index oid = .verified incumbent alternatives)
    (verified : verifier.verify oid bytes = .verified) (fresh : bytes ∉ incumbent :: alternatives) :
    (index.step verifier policies oid (.preimage bytes)).2.query oid = .ambiguous incumbent bytes alternatives := by
  rw [retain_collision policy present verified fresh]
  simp [Index.query, Index.put, Bucket.query]

theorem no_hit_after_dispute {updated : Index} {left right : ByteArray}
    (extended : index.Extends updated) (first : left ∈ (index oid).candidates)
    (second : right ∈ (index oid).candidates) (different : left ≠ right) : updated.query oid ≠ .hit bytes := by
  intro hit
  exact different ((hit_eq hit ((extended oid).2 first)).trans (hit_eq hit ((extended oid).2 second)).symm)

theorem canSeed_iff {Value : Type} {blocked : Disputes} {encode : Value → Option ByteArray} {left right : Value} :
    index.canSeed blocked encode oid left right = true ↔ index.Seed blocked encode oid left right := by
  cases query : index.query oid <;> simp [Index.canSeed, Index.Seed, query]

end Silmaril.Proofs.Formats.Git.Arena.Collision
