module

import Silmaril.Formats.Git.Native.Thms
meta import Silmaril.Formats.Git.Native.Thms

open Silmaril Silmaril.Formats.Git Silmaril.Formats.Git.Native
open Silmaril.Formats.Dasl.Prolly (ByteKey)

private def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def hexDigit? (char : Char) : Option Nat :=
  if '0' ≤ char ∧ char ≤ '9' then some (char.toNat - '0'.toNat)
  else if 'a' ≤ char ∧ char ≤ 'f' then some (10 + char.toNat - 'a'.toNat) else none

private def hexBytes? : List Char → Option (List UInt8)
  | [] => some []
  | high :: low :: rest => do
    let byte := UInt8.ofNat (16 * (← hexDigit? high) + (← hexDigit? low))
    return byte :: (← hexBytes? rest)
  | [_] => none

private def oid (algorithm : Algorithm) (text : String) : IO (NameBytes algorithm) := do
  let some bytes := hexBytes? text.toList >>= (nameBytes? algorithm ∘ List.toByteArray) |
    throw (IO.userError "invalid fixture object ID")
  pure bytes

private def repeated (algorithm : Algorithm) (byte : UInt8) : NameBytes algorithm :=
  ⟨⟨Array.replicate algorithm.width byte⟩, by simp [ByteArray.size]⟩

private def tree (algorithm : Algorithm) : Object ByteKey (NameBytes algorithm) CommitMetadata .tree :=
  let mode := fun key : ByteKey =>
    if key = Dasl.utf8Key "foo" then EntryMode.directory
    else if key = Dasl.utf8Key "sub" then .gitlink
    else if key = Dasl.utf8Key "foo0" then .file .symlink
    else if key = Dasl.utf8Key "foo." then .file .regular else .file .executable
  .tree {[255], Dasl.utf8Key "sub", Dasl.utf8Key "foo0", Dasl.utf8Key "foo", Dasl.utf8Key "foo."}
    (fun key => mode key.val) (fun key => .ref (mode key.val).kind (repeated algorithm
      (if key.val = Dasl.utf8Key "foo." then 0x11 else if key.val = Dasl.utf8Key "foo" then 0x22
        else if key.val = Dasl.utf8Key "foo0" then 0x33 else if key.val = Dasl.utf8Key "sub" then 0x44 else 0x55)))

private def metadata (message : String) : CommitMetadata :=
  ⟨⟨"Author", "a@example.test", 10⟩, ⟨"Committer", "c@example.test", 20⟩, message⟩

private def fixture (algorithm : Algorithm) (treeOID firstOID secondOID : String) : IO Unit := do
  let treeName ← oid algorithm treeOID
  let firstName ← oid algorithm firstOID
  let secondName ← oid algorithm secondOID
  let sizes := match algorithm with | .sha1 => (154, 142, 237) | .sha256 => (214, 166, 309)
  let expectedTree := ("tree " ++ toString sizes.1).toByteArray.push 0 ++
    "100644 foo.".toByteArray.push 0 ++ (repeated algorithm 0x11).val ++
    "40000 foo".toByteArray.push 0 ++ (repeated algorithm 0x22).val ++
    "120000 foo0".toByteArray.push 0 ++ (repeated algorithm 0x33).val ++
    "160000 sub".toByteArray.push 0 ++ (repeated algorithm 0x44).val ++
    ("100755 ".toByteArray.push 255).push 0 ++ (repeated algorithm 0x55).val
  let commitStart := "tree " ++ treeOID ++ "\n"
  let identities := "author Author <a@example.test> 10 +0000\ncommitter Committer <c@example.test> 20 +0000\n\n"
  let expectedParent := fun message : String =>
    ("commit " ++ toString sizes.2.1).toByteArray.push 0 ++ (commitStart ++ identities ++ message).toByteArray
  let assign := fun bytes : ByteArray =>
    if bytes = expectedTree then treeName
    else if bytes = expectedParent "base one\n" then firstName
    else if bytes = expectedParent "base two\n" then secondName else repeated algorithm 0
  let model : Profile algorithm ByteKey (NameBytes algorithm) := ⟨⟨id, some, fun _ => rfl⟩, nameBytesCodec algorithm, assign⟩
  let root := tree algorithm
  let ancestor : String → Object ByteKey (NameBytes algorithm) CommitMetadata .commit := fun message =>
    .commit root 0 Fin.elim0 (metadata message)
  let commit := Object.commit root 2 (fun index => ancestor (if index.val = 0 then "base two\n" else "base one\n"))
    (metadata "message\n")
  let some (.encoded preimage) := renderObject model root | throw (IO.userError "native tree")
  check (decide (preimage = expectedTree)) "Git mktree preimage"
  let some (.encoded commitBytes) := renderObject model commit | throw (IO.userError "native commit")
  let expectedCommit := ("commit " ++ toString sizes.2.2).toByteArray.push 0 ++
    (commitStart ++ "parent " ++ secondOID ++ "\nparent " ++ firstOID ++ "\n" ++ identities ++ "message\n").toByteArray
  check (decide (commitBytes = expectedCommit)) "Git commit-tree preimage"
  let invalid : Object ByteKey (NameBytes algorithm) CommitMetadata .tree :=
    .tree {[47]} (fun _ => .file .regular) (fun _ => .blob ByteArray.empty)
  check (renderObject model invalid).isNone "reject slash in a native name"
  let invalidMeta : CommitMetadata := { metadata "not accepted" with author := ⟨"Name\nOther", "n@x", 0⟩ }
  check (renderObject model (.commit root 0 Fin.elim0 invalidMeta)).isNone "reject injected commit header"

public def main : IO Unit := do
  check (decide (loose .blob "abc".toByteArray = "blob 3".toByteArray.push 0 ++ "abc".toByteArray))
    "blob header encodes exact payload byte length"
  check ((nameBytes? .sha1 ByteArray.empty).isNone && (nameBytes? .sha256 (repeated .sha1 0).val).isNone)
    "OID widths are checked"
  fixture .sha1 "fb4ea3bd811289b0f922112882b9d45b58b2b4e2"
    "a89421c2e1ec27febdce925a726141358daafe96" "93f180f72654a4c20745645676422e4c7b831c94"
  fixture .sha256 "7ac031ff6f6d51fcdf1782ffec080fb5d3d2fccd1629fbcea8aaa0e9ecd23a43"
    "706fb11574551ea4ea2ff0c05808dbbf744633e305f26b01057a5f3ac8bbf746"
    "2f2be9437a545ada8b59e000f28975768e320256a6009ce6f08d994ae8e25927"
  IO.println "Git native SHA-1 and SHA-256 checks passed"

#print axioms NameCodec
#print axioms loose_size
#print axioms treeOrder_sorted
#print axioms View.target_matches
#print axioms renderObject_toObject
#print axioms names_toObject
