module

import Batteries.Data.Except
import Silmaril.Formats.Git.Arena.Equality.Thms
meta import Silmaril.Formats.Git.Arena.Equality.Defs
meta import Silmaril.Formats.Git.Arena.Collision.Defs
meta import Silmaril.Formats.Git.Arena.Defs
meta import Silmaril.Formats.Git.Native.Defs
meta import Silmaril.Formats.Dasl.Encode.Defs
meta import Silmaril.Semantics.Arena.Defs

open Silmaril.Formats.Git
open Silmaril.Formats.Git.Arena
open Silmaril.Formats.Git.Arena.Collision (Index Policies Verifier)
open Silmaril.Formats.Git.Arena.Equality
open Silmaril.Formats.Dasl.Encode (PartialCodec)

private def first : ByteArray := "first".toUTF8
private def second : ByteArray := "other".toUTF8
private def anonymous : ByteArray := "nameless".toUTF8
private def firstWire : ByteArray := Native.loose .blob first
private def secondWire : ByteArray := Native.loose .blob second

private def digest (algorithm : Native.Algorithm) : Native.NameBytes algorithm :=
  ⟨⟨Array.replicate algorithm.width 7⟩, by simp [ByteArray.size]⟩

private def oid (algorithm : Native.Algorithm) : Oid := Oid.ofBytes algorithm (digest algorithm)

private def rawCid (digestTag : UInt8) : ByteArray := ⟨#[1, 0x55, 0x1e, 32] ++ Array.replicate 32 digestTag⟩

private def profile : Profile ByteArray ByteArray where
  kind _ := some .blob
  gitBytes _ payload := if payload = anonymous then none else some (Native.loose .blob payload)
  gitHash algorithm _ := some (digest algorithm)
  casBytes lane payload := if lane = .raw then some payload else none
  casName _ bytes := if bytes = first then some (rawCid 1) else if bytes = second then some (rawCid 2) else none

private def verifier : Verifier where
  admits _ bytes := decide (bytes = firstWire ∨ bytes = secondWire)
  digest algorithm _ := some (digest algorithm)

private def codec : PartialCodec ByteArray ByteArray where
  encode? value := if value = first then some firstWire else none
  decode? bytes := if bytes = firstWire then some first else none
  recovers := by
    intro value bytes encoded
    by_cases same : value = first <;> simp_all

private def authority : Sha256Authority ByteArray where
  accepts name bytes value := decide (name = digest .sha256 ∧ bytes = firstWire ∧ value = first)
  binds := by
    intro name bytes left right allowedLeft allowedRight
    simp only [decide_eq_true_eq] at allowedLeft allowedRight
    exact allowedLeft.2.2.trans allowedRight.2.2.symm

private abbrev Demo := Snapshot 6 ByteArray ByteArray
private abbrev Candidate := Request 6 ByteArray

private def request (left right : Fin 6) (evidence : Evidence ByteArray) : Candidate := ⟨left, right, evidence⟩

private def checked {Value : Type} (result : Except Arena.Fault Value) : Except String Value := result.mapError reprStr

private def check (message : String) (claim : Prop) [Decidable claim] : Except String Unit :=
  if claim then .ok () else .error message

private def addNamed (state : Arena.State 6 ByteArray ByteArray) (key : Fin 6) (bytes : ByteArray) :
    Except Arena.Fault (Arena.State 6 ByteArray ByteArray) := do
  let stored ← state.step profile key (.insert bytes)
  return (← stored.assign profile key (.cas .raw)).2

private def claimed : Index :=
  let afterSha1 := (Index.empty.step verifier (fun _ => .strict) (oid .sha1) .claim).2
  (afterSha1.step verifier (fun _ => .strict) (oid .sha256) .claim).2

private def acquired : Index :=
  let afterSha1 := (claimed.step verifier (fun _ => .strict) (oid .sha1) (.preimage firstWire)).2
  (afterSha1.step verifier (fun _ => .strict) (oid .sha256) (.preimage firstWire)).2

private def fixture : Except String Demo := do
  let base : Arena.State 6 ByteArray ByteArray := Silmaril.Semantics.Arena.State.empty
  let firstNamed ← checked (addNamed base 0 first)
  let aliased ← checked (addNamed firstNamed 1 first)
  let secondNamed ← checked (addNamed aliased 2 second)
  let anonymousLeft ← checked (secondNamed.step profile 3 (.insert anonymous))
  let anonymousBoth ← checked (anonymousLeft.step profile 4 (.insert anonymous))
  let waiting ← checked (anonymousBoth.step profile 5 (.reserve (.git (oid .sha256)) (some .blob)))
  return ⟨waiting, profile, fun _ => codec, claimed, fun _ => false, some authority⟩

private def equalityFixture : Except String Unit := do
  let pending ← fixture
  let sha1Claim := request 0 1 (.trustedGit (oid .sha1))
  let sha1Evidence := request 0 1 (.nativeBytes (oid .sha1))
  let sha256Trusted := request 0 1 (.trustedGit (oid .sha256))
  let shallow := request 0 5 (.trustedGit (oid .sha256))
  let rawCas := request 0 1 (.canonicalCas .raw (rawCid 1))
  let nameless := request 3 4 .content
  check "claims and shallow placeholders cannot seed"
    (pending.check sha1Claim = .error .trustUnavailable ∧ pending.check sha1Evidence = .error .nativeEvidence ∧
      pending.check sha256Trusted = .error .nonuniqueOid ∧ pending.check shallow = .error .nonresident)
  let observed := { pending with git := acquired }
  check "SHA-1 refuses label trust after observation, but recovering exact bytes suffice"
    (observed.check sha1Claim = .error .trustUnavailable ∧ observed.check sha1Evidence = .ok ())
  check "SHA-256 trust is explicitly configured and cannot materialize a placeholder"
    (observed.check sha256Trusted = .ok () ∧
      ({ observed with authority := none } : Demo).check sha256Trusted = .error .trustUnavailable ∧
      observed.check shallow = .error .nonresident)
  check "SHA-256 authority need not validate nameless payloads"
    (observed.check (request 3 4 (.trustedGit (oid .sha256))) = .error .untrusted)
  check "deterministic BLAKE3-shaped name with actual binding and nameless same-content both work"
    (observed.check rawCas = .ok () ∧ observed.check nameless = .ok () ∧
      profile.derive (.cas .raw) anonymous = none ∧ profile.derive (.git .sha256) anonymous = none)
  let noClaim := observed.arena.replaceAt 1 (some ⟨none, some first⟩)
  check "equal derived CAS names without two observed bindings do not seed"
    (({ observed with arena := noClaim } : Demo).check rawCas = .error .casUnbound)
  let overlap : Claims ByteArray := ⟨[.git (oid .sha256)], some .blob⟩
  let claimedClash := (observed.arena.replaceAt 0 (some ⟨some overlap, some first⟩)).replaceAt 2
    (some ⟨some overlap, some second⟩)
  check "different verified canonical names reject even with identical unchecked Git claims"
    (({ observed with arena := claimedClash } : Demo).check (request 0 2 (.trustedGit (oid .sha256))) =
      .error (.differentCas .raw))
  check "accepted edge agrees on real typed observations"
    (observed.typedAt codec codec.encode? 0 = some first ∧ observed.typedAt codec codec.encode? 1 = some first ∧
      observed.typedAt codec codec.encode? 5 = none)
  let candidates := [sha1Evidence, sha256Trusted, rawCas, nameless, shallow, sha1Claim]
  check "replay admits only validated edges" ((observed.replay candidates).length = 4)
  for algorithm in [Native.Algorithm.sha1, .sha256] do
    let identity := oid algorithm
    let onThis := if algorithm = .sha1 then sha1Evidence else sha256Trusted
    let onOther := if algorithm = .sha1 then sha256Trusted else sha1Evidence
    let (rejected, strict) := acquired.step verifier (fun _ => .strict) identity (.preimage secondWire)
    let afterNotice := ({ observed with git := strict } : Demo).deliver identity rejected
    check "strict collision leaves incumbent, but delivered notice invalidates dependent edge"
      (rejected = .rejectedCollision ∧ strict.query identity = .hit firstWire ∧
        afterNotice.check onThis = .error .oidBlocked ∧ afterNotice.check onOther = .ok () ∧
        (afterNotice.replay candidates).length = 3)
    let revoked := observed.revoke identity
    check "explicit revocation fails closed without needing a collision"
      (revoked.check onThis = .error .oidBlocked ∧ (revoked.replay candidates).length = 3)
    let (retained, disputed) := acquired.step verifier (fun _ => .retain) identity (.preimage secondWire)
    let disputedView : Demo := { observed with git := disputed }
    check "both algorithms lose unique evidence when retention exposes ambiguity"
      (retained = .retainedCollision ∧ disputed.query identity = .ambiguous firstWire secondWire [] ∧
        disputedView.check onThis = .error (if algorithm = .sha1 then .nativeEvidence else .nonuniqueOid) ∧
        (disputedView.replay candidates).length = 3)
    check "replay, delivery, and revocation leave independent raw BLAKE3-shaped CAS reads alone"
      (afterNotice.readRaw (rawCid 1) = .found first ∧ disputedView.readRaw (rawCid 2) = .found second ∧
        revoked.readRaw (rawCid 1) = .found first)

public def main : IO Unit := match equalityFixture with
  | .ok () => IO.println "Git equality replay: both SHA lanes, canonical/nameless content, and live distrust passed"
  | .error detail => throw (IO.userError detail)

#print axioms Snapshot.check_sound
#print axioms Snapshot.derived_different
#print axioms Snapshot.reject_different_cas
#print axioms Snapshot.check_oid_hit
#print axioms Snapshot.check_oid_verified
#print axioms Snapshot.mem_replay
#print axioms Snapshot.related_content
#print axioms Snapshot.related_typed
#print axioms Snapshot.related_readWire
#print axioms Snapshot.related_reject_different_cas
#print axioms Snapshot.related_monotone
#print axioms Snapshot.check_blocked
#print axioms Snapshot.replay_excludes_blocked
#print axioms Snapshot.replay_excludes_nonunique
#print axioms Snapshot.replay_after_delivery
#print axioms Snapshot.replay_after_revocation
#print axioms Snapshot.check_nonOid_frame
#print axioms Snapshot.readRaw_delivery
#print axioms Snapshot.readRaw_revocation
