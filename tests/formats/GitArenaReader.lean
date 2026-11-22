module

import Batteries.Data.Except
import Silmaril.Formats.Git.Arena.Reader.Thms
meta import Silmaril.Formats.Git.Arena.Reader.Defs
meta import Silmaril.Formats.Git.Arena.Defs
meta import Silmaril.Formats.Git.Native.Defs
meta import Silmaril.Formats.Dasl.Prolly.Route.Defs
meta import Silmaril.Semantics.Arena.Defs

open Silmaril.Formats.Git
open Silmaril.Formats.Git.Arena
open Silmaril.Formats.Dasl
open Silmaril.Semantics.Prolly (Block)

private def raw : ByteArray := "payload".toUTF8
private def native : ByteArray := Native.loose .blob raw
private def second : ByteArray := "other".toUTF8

private def digest (tag : UInt8) : Native.NameBytes .sha1 :=
  ⟨⟨Array.replicate 20 tag⟩, by simp [ByteArray.size, Native.Algorithm.width]⟩

private def profile : Profile String ByteArray where
  kind _ := some .blob
  gitBytes _ bytes := some (Native.loose .blob bytes)
  gitHash
    | .sha1, _ => some (digest 7)
    | .sha256, _ => none
  casBytes _ bytes := some bytes
  casName _ bytes :=
    if bytes = raw then some "raw-name" else if bytes = second then some "other-name" else none

private def decode (_ : Arena.Id String) (_ : ByteArray) : Option ByteArray := some raw

private def checked {Value : Type} (result : Except Fault Value) : Except String Value :=
  result.mapError reprStr

private def check (message : String) (claim : Prop) [Decidable claim] : Except String Unit :=
  if claim then .ok () else .error message

private def fails {Value : Type} (result : Except Fault Value) (expected : Fault) : Bool :=
  match result with | .ok _ => false | .error fault => decide (fault = expected)

private def lazyFixture : Except String Unit := do
  let empty : State 2 String ByteArray := Silmaril.Semantics.Arena.State.empty
  let cas : Arena.Id String := .cas .raw "raw-name"
  let oid : Arena.Id String := .git (.sha1 (digest 7))
  let wrong : Arena.Id String := .git (.sha1 (digest 8))
  let pending ← checked (empty.step profile 0 (.reserve cas))
  let byRaw := Descriptor.raw "raw-name"
  let byObject := Descriptor.object "raw-name" (fun _ => some true)
  check "raw descriptor observes placeholder" (byRaw.read (pending.casReader profile) = .placeholder)
  check "same CAS name on another lane does not bind it" (byObject.read (pending.casReader profile) = .unindexed)
  check "transient miss and defer remain distinct when loading"
    (fails (pending.cacheBytes profile 0 cas decode (fun _ => .missing)) .missing = true ∧
      fails (pending.cacheBytes profile 0 cas decode (fun _ => .deferred)) .deferred = true)
  check "permissive decoder cannot replace original CAS preimage"
    (fails (pending.cacheBytes profile 0 cas decode (fun _ => .found "alternate".toUTF8)) .invalid = true)
  let loaded ← checked (pending.cacheAndAssign profile 0 cas (.git .sha256) decode (fun _ => .found raw))
  check "Git digest unavailability keeps the loaded CAS object"
    (loaded.derivation = .error .unavailable ∧ byRaw.read (loaded.arena.casReader profile) = .found raw)
  let readback ← checked (loaded.arena.cacheAndAssign profile 0 cas (.git .sha1) decode (fun _ => .conflict))
  check "resident hit ignores reader and computes optional SHA-1 name"
    (readback.derivation = .ok oid ∧ readback.arena.readGit profile (.sha1 (digest 7)) = .found native)
  let secondRaw : Arena.Id String := .cas .raw "other-name"
  let reservedSecond ← checked (readback.arena.step profile 1 (.reserve secondRaw))
  let collision ← checked (reservedSecond.cacheAndAssign profile 1 secondRaw (.git .sha1)
    (fun _ _ => some second) (fun _ => .found second))
  check "failed secondary assignment neither rebinds Git nor rolls back a checked CAS read"
    (collision.derivation = .error .conflict ∧ collision.arena.readGit profile (.sha1 (digest 7)) = .found native ∧
      (Descriptor.raw "other-name").read (collision.arena.casReader profile) = .found second)
  let rejected ← checked (empty.step profile 0 (.reserve wrong (some .blob)))
  check "exact preimage alone does not imply a matching OID"
    (fails (rejected.cacheBytes profile 0 wrong decode (fun _ => .found native)) .invalid = true)
  let pendingGit ← checked (empty.step profile 0 (.reserve oid (some .blob)))
  let imported ← checked (pendingGit.cacheAndAssign profile 0 oid (.cas .raw) decode (fun _ => .found native))
  check "exact Git preimage can derive independent raw CAS bytes"
    (imported.derivation = .ok cas ∧ byRaw.read (imported.arena.casReader profile) = .found raw)
  check "decode failure is invalid, not absent"
    ((Descriptor.mk .raw "raw-name" (fun _ => (none : Option Bool))).read
      (imported.arena.casReader profile) = .invalid)
  check "descriptor keeps a rich fetch fault"
    (byObject.read (fun _ _ => .deferred) = .deferred ∧ byObject.read (fun _ _ => .conflict) = .conflict)

private def prollyFixture : Except String Unit := do
  let codec : Encode.PartialCodec (Block Nat String String) (Shallow Nat) := Prolly.blockCodec Encode.text Encode.text
  let rootBytes := "root".toUTF8
  let leafBytes := "leaf".toUTF8
  let parse : ByteArray → Option (Shallow Nat) := fun bytes =>
    if bytes = rootBytes then codec.encode? (.branch 1 [("k", 2)])
    else if bytes = leafBytes then codec.encode? (.leaf [("k", "value")]) else none
  let snapshot : CasReader Nat := fun lane name =>
    if lane = .raw then .conflict
    else match name with
      | 1 => .found rootBytes
      | 2 => .found leafBytes
      | 3 => .found "broken".toUTF8
      | _ => .missing
  let classify : Nat → ReadFault → Prolly.Fault Nat := fun name fault =>
    if fault = .missing then .missing name else .invalidWire name
  let route := Prolly.route (snapshot.prolly parse codec classify) 4
  check "typed Prolly reader routes through object lane only" (route "k" 2 none 1 = .ok (some "value"))
  check "confirmed route absence is not a missing block" (route "z" 2 none 1 = .ok none ∧
    route "k" 2 none 4 = .error (.missing 4) ∧ route "k" 2 none 3 = .error (.invalidWire 3))
  let delayed : CasReader Nat := fun lane name => if name = 2 then .deferred else snapshot lane name
  check "selected deferred block never becomes a successful absence"
    (Prolly.route (delayed.prolly parse codec classify) 4 "k" 2 none 1 = .error (.invalidWire 2))

public def main : IO Unit :=
  let checks : Except String Unit := do
    lazyFixture
    prollyFixture
  match checks with
  | .ok () => IO.println "Exact lazy Git/CAS intake and typed Prolly adapter: passed"
  | .error detail => throw (IO.userError detail)

#print axioms Descriptor.read_found
#print axioms Descriptor.read_fault
#print axioms CasReader.prolly_found
#print axioms Reader.exact_found
#print axioms State.descriptor_found
#print axioms State.cacheBytes_spec
#print axioms State.cacheBytes_at
#print axioms State.cacheAndAssign_spec
#print axioms State.cacheAndAssign_valid
#print axioms State.cacheAndAssign_extends
