module

import Silmaril.Formats.Git.Arena.Collision.Thms
meta import Silmaril.Formats.Git.Arena.Collision.Defs
meta import Silmaril.Formats.Git.Arena.Defs
meta import Silmaril.Formats.Git.Native.Defs
meta import Silmaril.Semantics.Arena.Defs

open Silmaril.Formats.Git
open Silmaril.Formats.Git.Arena
open Silmaril.Formats.Git.Arena.Collision

private def digest (algorithm : Native.Algorithm) (tag : UInt8) : Native.NameBytes algorithm :=
  ⟨⟨Array.replicate algorithm.width tag⟩, by simp [ByteArray.size]⟩

private def target (algorithm : Native.Algorithm) : Oid := Oid.ofBytes algorithm (digest algorithm 7)

private def blob (payload : ByteArray) : ByteArray := Native.loose .blob payload
private def first : ByteArray := blob "first".toUTF8
private def second : ByteArray := blob "other".toUTF8
private def wrongDigest : ByteArray := blob "mismatch".toUTF8
private def notComputed : ByteArray := blob "unavailable".toUTF8
private def malformed : ByteArray := "not an object".toUTF8

private def oracle : Verifier where
  admits _ bytes := decide (bytes ∈ [first, second, wrongDigest, notComputed])
  digest algorithm bytes :=
    if bytes = notComputed then none
    else some (digest algorithm (if bytes = wrongDigest then 9 else 7))

private def mixed : Policies
  | .sha1 => .strict
  | .sha256 => .retain

private def reversed : Policies
  | .sha1 => .retain
  | .sha256 => .strict

private def casProfile : Profile String ByteArray where
  kind _ := some .blob
  gitBytes _ _ := none
  gitHash _ _ := none
  casBytes lane bytes := if lane = .raw then some bytes else none
  casName _ bytes := if bytes = "first".toUTF8 then some "independent-name" else none

private def check (message : String) (claim : Prop) [Decidable claim] : Except String Unit :=
  if claim then .ok () else .error message

private def exercise (algorithm : Native.Algorithm) (policies : Policies) : Except String Unit := do
  let base : State 1 String ByteArray := Silmaril.Semantics.Arena.State.empty
  let named ← (do
    let stored ← base.step casProfile 0 (.insert "first".toUTF8)
    return (← stored.assign casProfile 0 (.cas .raw)).2).mapError (fun fault => reprStr fault)
  let initial : Store 1 String ByteArray := ⟨Index.empty, named⟩
  let oid := target algorithm
  let other := target (if algorithm = .sha1 then .sha256 else .sha1)
  let clear : Disputes := fun _ => false
  check "algorithm dispatch stays in its own lane" (oid.algorithm = algorithm ∧ oid ≠ other)
  let (claimResult, placeholder) := initial.step oracle policies oid .claim
  check "claim records only a placeholder" (claimResult = .claimed ∧ placeholder.git.query oid = .unverified)
  check "unverified OID cannot seed equality" (placeholder.git.canSeed clear some oid first first = false)
  let (repeated, placeholder) := placeholder.step oracle policies oid .claim
  check "repeated claim stays unverified" (repeated = .unverified ∧ placeholder.git.query oid = .unverified)
  let (missingResult, placeholder) := placeholder.step oracle policies oid .missing
  check "transient missing keeps the placeholder" (missingResult = .missing ∧ placeholder.git.query oid = .unverified)
  let (bad, placeholder) := placeholder.step oracle policies oid (.preimage malformed)
  check "corrupt native object is not a collision" (bad = .malformed ∧ placeholder.git.query oid = .unverified)
  let (bad, placeholder) := placeholder.step oracle policies oid (.preimage wrongDigest)
  check "mismatching digest is not a collision" (bad = .mismatch ∧ placeholder.git.query oid = .unverified)
  let (unknown, placeholder) := placeholder.step oracle policies oid (.preimage notComputed)
  check "unavailable digest does not materialize the claim"
    (unknown = .unavailable ∧ placeholder.git.query oid = .unverified)
  let (insertResult, resident) := placeholder.step oracle policies oid (.preimage first)
  check "first verified observation" (insertResult = .inserted ∧ resident.git.query oid = .hit first)
  check "verified matching endpoint bytes can seed" (resident.git.canSeed clear some oid first first = true)
  check "equal digest does not seed unequal endpoint bytes" (resident.git.canSeed clear some oid first second = false)
  let (duplicateResult, resident) := resident.step oracle policies oid (.preimage first)
  check "exact duplicate is not a collision" (duplicateResult = .duplicate ∧ resident.git.query oid = .hit first)
  let (collision, after) := resident.step oracle policies oid (.preimage second)
  match policies algorithm with
  | .strict =>
    check "strict has no replacement" (collision = .rejectedCollision ∧ after.git.query oid = .hit first)
  | .retain =>
    check "retain is explicitly ambiguous"
      (collision = .retainedCollision ∧ after.git.query oid = .ambiguous first second [])
    check "ambiguity cannot seed even with matching endpoints" (after.git.canSeed clear some oid first first = false)
    let (again, unchanged) := after.step oracle policies oid (.preimage second)
    check "reobserving a retained candidate is idempotent"
      (again = .duplicate ∧ unchanged.git.query oid = .ambiguous first second [])
  let blocked := clear.record oid collision
  check "collision notice blocks even strict incumbent seeding" (after.git.canSeed blocked some oid first first = false)
  check "other Git lane untouched" (after.git.query other = .unindexed ∧ blocked other = false)
  check "independent raw CAS still reads" (after.readRaw casProfile "independent-name" = .found "first".toUTF8)

private def mixedTrace : Except String Unit := do
  let sha1Oid := target .sha1
  let sha256Oid := target .sha256
  let clean : List Event := [(sha1Oid, .claim), (sha256Oid, .preimage first),
    (sha1Oid, .missing), (sha1Oid, .preimage first), (sha256Oid, .preimage first)]
  let (outcomes, both) := Index.empty.run oracle mixed clean
  let (reversedOutcomes, reversedBoth) := Index.empty.run oracle reversed clean
  check "collision-free interleaving agrees under mixed and reversed policies"
    (outcomes = [.claimed, .inserted, .missing, .inserted, .duplicate] ∧ reversedOutcomes = outcomes ∧
      both.query sha1Oid = .hit first ∧ both.query sha256Oid = .hit first ∧
      reversedBoth.query sha1Oid = .hit first ∧ reversedBoth.query sha256Oid = .hit first)
  let bothCollide : List Event := [(sha1Oid, .preimage second), (sha256Oid, .preimage second)]
  let (outcomes, divergent) := both.run oracle mixed bothCollide
  let (reversedOutcomes, reversedDivergent) := reversedBoth.run oracle reversed bothCollide
  check "same mixed index applies distinct policies to the simultaneous known OIDs"
    (outcomes = [.rejectedCollision, .retainedCollision] ∧ divergent.query sha1Oid = .hit first ∧
      divergent.query sha256Oid = .ambiguous first second [] ∧ reversedOutcomes = outcomes.reverse ∧
      reversedDivergent.query sha1Oid = .ambiguous first second [] ∧ reversedDivergent.query sha256Oid = .hit first)

public def main : IO Unit := do
  for algorithm in [Native.Algorithm.sha1, .sha256] do
    for policies in [mixed, reversed] do
      match exercise algorithm policies with
      | .ok () => IO.println s!"{repr algorithm} / {repr (policies algorithm)}: passed"
      | .error detail => throw (IO.userError detail)
  match mixedTrace with
  | .ok () => IO.println "Interleaved independent SHA-1/SHA-256 policies: passed"
  | .error detail => throw (IO.userError detail)

#print axioms Verifier.verified_iff
#print axioms Index.empty_valid
#print axioms Index.step_frame
#print axioms Index.step_valid
#print axioms Index.step_extends
#print axioms Index.step_missing
#print axioms Index.step_claim
#print axioms Index.step_failed_preimage
#print axioms Index.step_duplicate
#print axioms Index.step_strict_collision
#print axioms Index.step_retain_collision
#print axioms Index.query_retain_collision
#print axioms Index.first_collision
#print axioms Index.query_hit_verified
#print axioms Index.no_hit_after_dispute
#print axioms Index.run_valid
#print axioms Index.run_agree
#print axioms Store.step_cas
#print axioms Store.step_readRaw
#print axioms Store.step_strict_collision
#print axioms Disputes.record_blocked
#print axioms Disputes.record_preserves
#print axioms Index.canSeed_iff
#print axioms Index.seed_refuse_blocked
#print axioms Index.seed_refuse_nonhit
#print axioms Index.seed_verified
#print axioms Index.seed_sound
