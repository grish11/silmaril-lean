module

import Silmaril.Formats.Git.Dasl.Layouts.Thms
meta import Silmaril.Formats.Git.Dasl.Layouts.Thms

open Silmaril.Formats.Git Silmaril.Formats.Git.Dasl
open Silmaril.Formats.Dasl
open Silmaril.Formats

private def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def namer : Naming Nat where
  object
    | .dict keys _ => keys.card
    | .list count _ => count
    | _ => 0
  blob := ByteArray.size

private def policy (Key : Type) : Silmaril.Semantics.Prolly.Policy Key := ⟨2, by decide, fun _ _ => false⟩

private def leaf : Git.Tree := .file .symlink "target".toByteArray
private def emptyDir : Git.Tree := .dir ∅ (fun name => False.elim (Finset.notMem_empty _ name.property))

private def sampleEntries : ShallowTree String Nat :=
  ⟨{"z", "é", "sub"}, fun name => if name.val = "sub" then ⟨.gitlink, 700⟩ else ⟨.file .symlink, 6⟩⟩

private def directoryChecks : IO Unit := do
  let some entryName := Component.parse? "é" | throw (IO.userError "UTF-8 path component")
  let some dirName := Component.parse? "nested" | throw (IO.userError "directory component")
  let some nested := emptyDir.insert entryName leaf | throw (IO.userError "insert")
  let some outer := emptyDir.insert dirName nested | throw (IO.userError "nested insert")
  check (decide ((outer.lookup [dirName, entryName]).map Git.Tree.tag = some (.file .symlink))) "nested mode"
  let some removed := nested.remove entryName | throw (IO.userError "remove")
  check (removed.lookup [entryName]).isNone "removed child"
  let some malformed := (Git.Tree.dir {"bad/name"} (fun _ => leaf)).insert entryName leaf |
    throw (IO.userError "insert into raw tree")
  check ((renderTree namer .dict malformed).isNone) "invalid path component rejected by renderer"
  for layout in [Layout.dict, .stringList, .utf8List, .stringProlly (policy String), .utf8Prolly (policy Prolly.ByteKey)] do
    check ((renderTree namer layout outer).isSome) "valid tree renders in every layout"
  check ((decodeUtf8Key [255]).isNone && validByteComponent [255]) "native names can be non-UTF-8"
  check (decodeUtf8Key (utf8Key "é") == some "é") "UTF-8 roundtrip"

private def codecChecks : IO Unit := do
  let pairs : Encode.TotalCodec (ShallowTree String Nat) (Shallow Nat) := pairDirectory Encode.text
  let rawPairs : Encode.TotalCodec (ShallowTree Prolly.ByteKey Nat) (Shallow Nat) := pairDirectory Prolly.byteKey
  match pairs.encode sampleEntries with
  | .list 3 values =>
    match values 0 with
    | .list 2 entry =>
      match entry 0 with
      | .string "sub" => pure ()
      | _ => throw (IO.userError "ordered text keys")
    | _ => throw (IO.userError "expected a two-element entry array")
  | _ => throw (IO.userError "expected three entries")
  check (decide ((pairs.decode? (pairs.encode sampleEntries)).bind (·.lookup "sub") = some ⟨.gitlink, 700⟩))
    "pair-list gitlink"
  let bytes := sampleEntries.rekey utf8KeyCodec
  check (decide ((rawPairs.decode? (rawPairs.encode bytes)).bind (·.lookup (utf8Key "é")) = some ⟨.file .symlink, 6⟩))
    "byte-key list"
  check ((pairs.decode? (dictDirectory.encode sampleEntries)).isNone) "list decoder rejects dictionary layout"
  let invalid : Shallow Nat := .dict entryKeys (fun key => if key.val = "mode" then .i64 40960 else .ref (.obj 6))
  check (decodeEntry invalid).isNone "a symlink must have a raw blob link"
  let commit : Commit Nat Nat Metadata := ⟨42, [9, 4, 9], ⟨"commit".toByteArray, -5⟩⟩
  let codec := namedCommit metadataCodec
  check (decide (codec.decode? (codec.encode commit) = some commit)) "commit preserves order and metadata"
  let some (root, _) := (Layout.stringProlly (policy String)).encode? namer sampleEntries |
    throw (IO.userError "Prolly encoding")
  match (Prolly.blockCodec Encode.text entryCodec).decode? root with
  | some (.branch 1 children) => check (children.length == 2) "Prolly root splits three entries"
  | _ => throw (IO.userError "expected a Prolly branch")

private def objectChecks : IO Unit := do
  let directory : Object String Nat Metadata .tree := .tree {"nested", "sub", "link"}
    (fun name => if name.val = "nested" then .directory else if name.val = "sub" then .gitlink else .file .symlink)
    (fun name => by
      split
      · exact .ref .tree 80
      · split
        · exact .ref .commit 700
        · exact .blob "target".toByteArray)
  let commit : Object String Nat Metadata .commit :=
    .commit directory 2 (fun index => .ref .commit (10 + index.val)) ⟨ByteArray.empty, 0⟩
  check ((renderObject namer .dict validComponent metadataCodec commit).isSome)
    "unavailable gitlink, subtree and parents do not prevent encoding"
  let shallow := directory.treeEntries? (fun object => (renderObject namer .dict validComponent metadataCodec object).map (·.root))
  check (decide (shallow.bind (·.lookup "sub") = some ⟨.gitlink, some 700⟩)) "opaque gitlink retains its name"
  check (decide (shallow.bind (·.lookup "link") = some ⟨.file .symlink, some 6⟩)) "symlink retains blob kind"

public def main : IO Unit := do
  directoryChecks
  codecChecks
  objectChecks
  IO.println "Git DASL checks passed"

#print axioms treeEquiv
#print axioms Directory.eq_of_lookup
#print axioms Directory.lookup_insert
#print axioms Directory.lookup_remove
#print axioms Directory.ofOrdered_ordered
#print axioms entryCodec
#print axioms utf8KeyCodec
#print axioms namedCommit
#print axioms dictDirectory
#print axioms pairDirectory
#print axioms Layout.prolly_stored
#print axioms renderObject_toObject
#print axioms names_toObject
