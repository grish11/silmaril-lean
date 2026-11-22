module

import Batteries.Data.Except
import Silmaril.Formats.Git.Filesystem.Routed.Thms
meta import Silmaril.Formats.Cbor.Drisl.Cid.Defs
meta import Silmaril.Formats.Git.Arena.Defs
meta import Silmaril.Formats.Git.Filesystem.Defs
meta import Silmaril.Formats.Git.Filesystem.Routed.Defs
meta import Silmaril.Formats.Git.Native.Defs
meta import Silmaril.Semantics.Arena.Defs

open Silmaril.Formats.Git
open Silmaril.Formats.Git.Arena (CasLane Read)
open Silmaril.Formats.Git.Filesystem
open Silmaril.Formats.Dasl.Prolly (ByteKey)

private abbrev Item := Σ mode : EntryMode, Object ByteKey String Unit mode.kind
private abbrev Snapshot := Object ByteKey String Unit .tree

private def emptyDir : Directory ByteKey Item := ⟨∅, fun key => False.elim (Finset.notMem_empty _ key.property)⟩

private def toTree (dir : Directory ByteKey Item) : Snapshot :=
  .tree dir.keys (fun key => (dir.get key).1) (fun key => (dir.get key).2)

private def nativeRaw : ByteKey := [255]
private def dirKey : ByteKey := Dasl.utf8Key "dir"
private def symlinkKey : ByteKey := Dasl.utf8Key "link"
private def body : ByteArray := "echo ok\n".toByteArray
private def symlinkBody : ByteArray := "dir/".toByteArray.push 255

private def fixtureFrom (body symlinkBody : ByteArray) : Snapshot :=
  let nested := toTree (emptyDir.insert nativeRaw ⟨.file .executable, .blob body⟩)
  toTree ((emptyDir.insert dirKey ⟨.directory, nested⟩).insert symlinkKey ⟨.file .symlink, .blob symlinkBody⟩)

private def mock (wire : ByteArray) : Digest :=
  let stamp := wire.toList.foldl (fun total byte => total * 65599 + byte.toUInt64) (0 : UInt64)
  ⟨(List.ofFn fun index : Fin 8 => (stamp >>> (8 * index.val.toUInt64)).toUInt8) ++ List.replicate 24 0, by simp⟩

private def require (message : String) (claim : Prop) [Decidable claim] : Except String Unit :=
  if claim then .ok () else .error message

private def arenaProfile (hash : Hash) : Arena.Profile Cid ByteArray where
  kind := fun _ => none
  gitBytes := fun _ _ => none
  gitHash := fun _ _ => none
  casBytes := fun _ bytes => some bytes
  casName lane bytes := some (address hash lane bytes)

private def arenaStore (hash : Hash) (writes : Writes) : Except String Store := do
  let profile := arenaProfile hash
  let empty : Arena.State writes.length Cid ByteArray := Silmaril.Semantics.Arena.State.empty
  let resident ← (List.finRange writes.length).foldlM (init := empty) fun state index => do
    let (cid, bytes) := writes[index.val]
    let lane : CasLane := if laneMatches .raw cid then .raw else .object
    let occupied ← (state.step profile index (.insert bytes)).mapError fun fault => reprStr fault
    let (id, named) ← (occupied.assign profile index (.cas lane)).mapError fun fault => reprStr fault
    require "arena assigned the canonical address" (id = .cas lane cid)
    pure named
  pure (Store.ofArena profile resident)

private def checkMount (hash : Hash) (mount : Store) (root : Cid)
    (resolve : Cid → List ByteKey → Except ReadFault (Option (Entry Cid))) : Except String Unit := do
  let .ok (some binary) := resolve root [dirKey, nativeRaw] | .error "missing executable at raw path"
  require "raw name has no UTF-8 façade spelling" (Dasl.decodeComponent nativeRaw = none)
  require "executable and bytes roundtrip" (binary.mode = .file .executable ∧ openBlob hash mount binary = .found body)
  let .some link := Component.parse? "link" | .error "invalid fixture name"
  let .ok (some symlink) := resolve root [Dasl.utf8Key link.val] | .error "missing symlink at UTF-8 byte path"
  require "symlink mode and target bytes preserved" (symlink.mode = .file .symlink ∧
    openBlob hash mount symlink = .found symlinkBody)
  require "no implicit symlink following" (resolve root [symlinkKey, nativeRaw] = .error .notDirectory)
  require "canonical directory absence" (resolve root [dirKey, Dasl.utf8Key "absent"] = .ok none)

private def exercise (hash : Hash) (fixture : Snapshot) : Except String Cid := do
  let staged ← (stage hash fixture).mapError fun fault => reprStr fault
  let .ok published := staged.publish (fun _ => none) | .error "fixture has an address conflict"
  require "raw and object lanes use different envelopes" (address hash .raw body ≠ address hash .object body)
  let arena ← arenaStore hash staged.writes
  for mount in [Store.ofPublished published, arena] do
    checkMount hash mount staged.name (locate hash mount 8)
    checkMount hash mount staged.name (locateRouted hash mount 8)
    checkMount hash mount staged.name (locateResident hash mount (staged.writes.map Prod.fst) 8)
    let .some link := Component.parse? "link" | .error "invalid fixture name"
    require "String facade is exact UTF-8"
      (locateUtf8 hash mount 8 staged.name [link] = locateRouted hash mount 8 staged.name [symlinkKey])
  let blocked : Store := fun lane cid =>
    if cid = staged.name then .deferred else (Store.ofPublished published) lane cid
  require "deferred block is not an absent path"
    (locate hash blocked 8 staged.name [dirKey] = .error (.deferred staged.name))
  require "routed deferred block is still a read fault"
    (locateRouted hash blocked 8 staged.name [dirKey] = .error (.deferred staged.name))
  let gitlink := toTree (emptyDir.insert dirKey ⟨.gitlink, .ref .commit "external-commit"⟩)
  let .error (.gitlink key) := stage hash gitlink | .error "gitlink imported as a local subtree"
  require "gitlink retains its boundary key" (key = dirKey)
  let wrongName := toTree (emptyDir.insert [0] ⟨.file .regular, .blob body⟩)
  let .error (.component key) := stage hash wrongName | .error "invalid NUL component accepted"
  require "component rejection reports its byte key" (key = [0])
  match staged.publish (fun cid => if cid = staged.name then some ByteArray.empty else none) with
  | .ok _ => .error "publication overwrote conflicting bytes"
  | .error cid =>
    require "conflicting root stays unchanged" (cid = staged.name)
    pure staged.name

private def checkPartial : Except String Unit := do
  let wide := (List.range 33).foldl (fun dir offset =>
    dir.insert [Fin.ofNat 256 (offset + 1)] ⟨.file .regular, .blob body⟩) emptyDir
  let image ← (stage mock (toTree wide)).mapError fun fault => reprStr fault
  let .ok published := image.publish (fun _ => none) | .error "wide fixture has a collision"
  let mount := Store.ofPublished published
  let .ok (.branch 1 [(_, first), (_, last)]) := dirReader mock mount image.name |
    .error "wide fixture did not produce exactly two leaves"
  let partialStore : Store := fun lane cid => if cid = last then .missing else mount lane cid
  let expected := .ok (some ⟨.file .regular, address mock .raw body⟩)
  require "full scan and route agree" (lookupChild mock mount 2 image.name [1] = expected ∧
    lookupChildRouted mock mount 2 image.name [1] = expected)
  require "route does not fetch unrelated sibling" (lookupChildRouted mock partialStore 2 image.name [1] = expected)
  require "scan still requires sibling" (lookupChild mock partialStore 2 image.name [1] = .error (.block (.missing last)))
  require "resident needs only the selected path"
    (lookupChildResident mock mount [image.name, first] 2 image.name [1] = expected)
  require "unacquired selected block is not absence"
    (lookupChildResident mock mount [image.name, first] 2 image.name [33] = .error (.block (.missing last)))
  require "unavailable selected block is not absence"
    (lookupChildRouted mock partialStore 2 image.name [33] = .error (.block (.missing last)))
  require "verified separator can prove absence without a leaf"
    (lookupChildRouted mock partialStore 2 image.name [34] = .ok none)
  require "fuel exhaustion is not absence"
    (lookupChildRouted mock partialStore 1 image.name [1] = .error (.block (.fuel first)))
  let malformed := address mock .object (ByteArray.mk #[255])
  let wrongWire : Store := fun _ _ => .found (ByteArray.mk #[255])
  require "malformed object bytes are not absence"
    (lookupChildRouted mock wrongWire 2 malformed [1] = .error (.block (.invalidWire malformed)))

private def parseNibble (char : Char) : Option Nat :=
  if '0' ≤ char ∧ char ≤ '9' then some (char.toNat - '0'.toNat)
  else if 'a' ≤ char ∧ char ≤ 'f' then some (10 + char.toNat - 'a'.toNat)
  else none

private def parseHex : List Char → Option (List UInt8)
  | [] => some []
  | high :: low :: rest => do
    let high ← parseNibble high
    let low ← parseNibble low
    return (UInt8.ofNat (16 * high + low)) :: (← parseHex rest)
  | [_] => none

private def externalDigest (command : String) (wire : ByteArray) : IO Digest :=
  IO.FS.withTempFile fun _ path => do
    IO.FS.writeBinFile path wire
    let output ← IO.Process.output { cmd := command, args := #[path.toString] }
    let some text := (output.stdout.splitOn " ").head? | throw (IO.userError "missing b3sum digest")
    let some bytes := parseHex text.toList | throw (IO.userError "invalid hex from b3sum")
    if width : bytes.length = 32 then
      if output.exitCode = 0 then pure ⟨bytes, width⟩ else throw (IO.userError "b3sum failed")
    else throw (IO.userError "b3sum produced a non-32-byte digest")

private abbrev DigestTable := List (ByteArray × Digest)

private def tableHash (seen : DigestTable) : Hash := fun wire =>
  ((seen.find? fun entry => decide (entry.1 = wire)).map Prod.snd).getD ⟨List.replicate 32 0, by simp⟩

/-- Only fixture preimages are supplied by the external hash executable. Iterate
until every block in the final replay has a checked fixture digest. -/
private def calculateFixture (command : String) (fixture : Snapshot) : Nat → DigestTable → IO DigestTable
  | 0, _ => throw (IO.userError "external digest table did not stabilize")
  | fuel + 1, seen => do
    let hash := tableHash seen
    let .ok image := stage hash fixture | throw (IO.userError "fixture staging failed")
    let missing := image.writes.filterMap fun (_, wire) =>
      if seen.any (fun entry => decide (entry.1 = wire)) then none else some wire
    if missing.isEmpty then pure seen else
      let more ← missing.mapM fun wire => do pure (wire, ← externalDigest command wire)
      calculateFixture command fixture fuel (seen ++ more)

private def oid (algorithm : Native.Algorithm) (path : System.FilePath) : IO (Native.NameBytes algorithm) := do
  let text ← IO.FS.readFile path
  let some bytes := parseHex text.trimAscii.toString.toList | throw (IO.userError s!"invalid Git OID: {path}")
  let some name := Native.nameBytes? algorithm bytes.toByteArray | throw (IO.userError s!"wrong OID width: {path}")
  pure name

private def nativeFixture (algorithm : Native.Algorithm) (directory : System.FilePath) : IO Snapshot := do
  let nested ← oid algorithm (directory / "nested.oid")
  let binary ← oid algorithm (directory / "executable.oid")
  let symlink ← oid algorithm (directory / "symlink.oid")
  let empty : ShallowTree ByteKey (Native.NameBytes algorithm) := ⟨∅,
    fun key => False.elim (Finset.notMem_empty _ key.property)⟩
  let codec := Native.nameBytesCodec algorithm
  let expectedNested := empty.insert nativeRaw ⟨.file .executable, binary⟩
  let expectedRoot := (empty.insert dirKey ⟨.directory, nested⟩).insert symlinkKey ⟨.file .symlink, symlink⟩
  let nestedBytes ← IO.FS.readBinFile (directory / "nested.tree")
  let rootBytes ← IO.FS.readBinFile (directory / "root.tree")
  unless Native.treePayload? codec expectedNested = some nestedBytes ∧ Native.treePayload? codec expectedRoot = some rootBytes do
    throw (IO.userError "Git tree bytes do not exactly match the modeled names, modes and original OIDs")
  let contents ← IO.FS.readBinFile (directory / "executable.blob")
  let target ← IO.FS.readBinFile (directory / "symlink.blob")
  let rootOid ← IO.FS.readFile (directory / "root.oid")
  IO.println s!"Git native {repr algorithm} tree {rootOid.trimAscii.toString}: exact tree bytes checked"
  pure (fixtureFrom contents target)

public def main (args : List String) : IO Unit := do
  if let .error detail := checkPartial then throw (IO.userError detail)
  let synthetic := fixtureFrom body symlinkBody
  let (fixture, hash) ← match args with
    | [] => pure (synthetic, mock)
    | [command] => pure (synthetic, tableHash (← calculateFixture command synthetic 8 []))
    | [command, algorithm, directory] =>
      let gitFormat ← match algorithm with
        | "sha1" => pure Native.Algorithm.sha1
        | "sha256" => pure Native.Algorithm.sha256
        | _ => throw (IO.userError "Git format must be sha1 or sha256")
      let source ← nativeFixture gitFormat ⟨directory⟩
      pure (source, tableHash (← calculateFixture command source 8 []))
    | _ => throw (IO.userError "usage: GitFilesystem.lean [b3sum [sha1|sha256 witness-directory]]")
  match exercise hash fixture with
  | .ok cid =>
    let text := (Silmaril.Formats.Cbor.Drisl.Cid.codec .bdasl).render cid
    IO.println s!"Git tree → BDASL → CID-only reads passed; tree CID {text}"
  | .error detail => throw (IO.userError detail)

#print axioms names_iff
#print axioms Image.publish_bindings
#print axioms Image.readPublished
#print axioms readVerified_found
#print axioms lookupChild_sound
#print axioms checkedChild_error
#print axioms lookupChildRouted_sound
#print axioms lookupChildResident_sound
#print axioms lookupChildRouted_agrees_scan
#print axioms locateWith_agree
