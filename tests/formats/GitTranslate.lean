module

import Silmaril.Crypto.SHA1.Thms
import Silmaril.Crypto.SHA256
import Silmaril.Formats.Dasl.Wire.Defs
import Silmaril.Formats.Git.Dasl.Layouts.Thms
import Silmaril.Formats.Git.Translate.Graph.Thms
meta import Silmaril.Crypto.SHA1.Thms
meta import Silmaril.Crypto.SHA256
meta import Silmaril.Formats.Dasl.Wire.Defs
meta import Silmaril.Formats.Git.Dasl.Layouts.Thms
meta import Silmaril.Formats.Git.Translate.Graph.Defs

open Silmaril Silmaril.Formats.Git Silmaril.Formats.Git.Translate
open Silmaril.Formats.Git.Translate.Graph
open Silmaril.Formats.Dasl (Shallow)
open Silmaril.Formats.Dasl.Wire (Cid)

private def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def repeated (algorithm : Native.Algorithm) (byte : UInt8) : Native.NameBytes algorithm :=
  ⟨⟨Array.replicate algorithm.width byte⟩, by simp [ByteArray.size]⟩

private def nativeHash : (algorithm : Native.Algorithm) → ByteArray → Native.NameBytes algorithm
  | .sha1, wire => ⟨(Crypto.sha1 wire.toList).toByteArray, by simp [Native.Algorithm.width, Crypto.SHA1.digest_length]⟩
  | .sha256, wire => ⟨(Crypto.SHA256.digest wire.toList).toByteArray,
      by simp [Native.Algorithm.width, Crypto.SHA256.digest_length]⟩

private def objectZero : Cid := ⟨[1, 0x71, 0x12, 32] ++ List.replicate 32 0, by decide⟩
private def rawZero : Cid := ⟨[1, 0x55, 0x12, 32] ++ List.replicate 32 0, by decide⟩

private def cidHash (tag : UInt8) (wire : ByteArray) : Option Cid :=
  (Formats.Cbor.Drisl.Cid.codec .dasl).parse? ([1, tag, 0x12, 32] ++ Crypto.SHA256.digest wire.toList)

private def objectBytes? := Formats.Dasl.Wire.render?

private def namer : Dasl.Naming Cid :=
  ⟨fun value => ((objectBytes? value).bind (cidHash 0x71)).getD objectZero,
    fun wire => (cidHash 0x55 wire).getD rawZero⟩

private def model (algorithm : Native.Algorithm) (layout : Dasl.Layout String Cid) :
    Profile algorithm String (Native.NameBytes algorithm) Cid Metadata where
  native := ⟨Dasl.utf8KeyCodec, Native.nameBytesCodec algorithm, nativeHash algorithm⟩
  naming := namer
  layout := layout
  valid := validComponent
  metadata := fun data => ⟨data.message.toByteArray, Int64.ofNat data.committer.seconds⟩
  codec := Dasl.metadataCodec
  frontier := fun kind name =>
    if decide (kind = .commit) && name.val == (repeated algorithm 0x77).val then
      cidHash 0x71 "external".toByteArray
    else none

private def tree (algorithm : Native.Algorithm) : Object String (Native.NameBytes algorithm) Native.CommitMetadata .tree :=
  .tree {"a", "b", "sub"}
    (fun key => if key.val = "sub" then .gitlink else .file (if key.val = "a" then .regular else .symlink))
    (fun key => by
      split
      · exact .ref .commit (repeated algorithm 0x77)
      · exact .blob "payload\n".toByteArray)

private def metadata (message : String) : Native.CommitMetadata :=
  ⟨⟨"Author", "a@example.test", 10⟩, ⟨"Committer", "c@example.test", 20⟩, message⟩

private def hex (bytes : ByteArray) : String :=
  let digit := fun value : Nat => Char.ofNat (if value < 10 then 48 + value else 87 + value)
  String.ofList (bytes.toList.flatMap fun byte => [digit (byte.toNat / 16), digit (byte.toNat % 16)])

private def exercise (algorithm : Native.Algorithm) (expected : String) : IO Cid := do
  let profile := model algorithm .dict
  let root := tree algorithm
  let ancestor (message : String) := Object.commit root 0 Fin.elim0 (metadata message)
  let merge := Object.commit root 3 (fun index => ancestor (if index.val = 1 then "one\n" else "two\n"))
    (metadata "merge\n")
  let some gitlink := translate profile (.ref .commit (repeated algorithm 0x77)) |
    throw (IO.userError "mapped gitlink should remain an opaque link")
  check ((translate profile (.ref .tree (repeated algorithm 0x77))).isNone) "frontier map is kind-specific"
  check ((translate { profile with frontier := fun _ _ => none } merge).isNone) "unmapped gitlink rejects fold"
  let some translated := translate profile merge | throw (IO.userError "translate dictionary commit")
  let some targetTree := translate profile root | throw (IO.userError "translate dictionary tree")
  let some first := translate profile (ancestor "one\n") | throw (IO.userError "translate first parent")
  let some second := translate profile (ancestor "two\n") | throw (IO.userError "translate second parent")
  let targetEntries : ShallowTree String Cid := ⟨{"a", "b", "sub"}, fun key =>
    if key.val = "sub" then ⟨.gitlink, gitlink.target.root⟩ else
      ⟨.file (if key.val = "a" then .regular else .symlink), namer.blob "payload\n".toByteArray⟩⟩
  let some treeBytes := objectBytes? (Dasl.dictDirectory.encode targetEntries) |
    throw (IO.userError "canonical dictionary tree bytes")
  check ((cidHash 0x71 treeBytes).map Subtype.val == some targetTree.target.root.val)
    "gitlink remains an object link and regular file and symlink share a raw link"
  let targetCommit := (Dasl.namedCommit Dasl.metadataCodec).encode
    ⟨targetTree.target.root, [second.target.root, first.target.root, second.target.root], ⟨"merge\n".toByteArray, 20⟩⟩
  let some targetBytes := objectBytes? targetCommit | throw (IO.userError "canonical commit bytes")
  check ((cidHash 0x71 targetBytes).map Subtype.val == some translated.target.root.val)
    "bottom-up commit hashes the canonical bytes with ordered, repeated parents"
  let some parsed := (Formats.Dasl.Wire.parse? targetBytes).bind (Dasl.namedCommit Dasl.metadataCodec).decode? |
    throw (IO.userError "canonical commit roundtrip")
  check (parsed.parents.map Subtype.val == [second.target.root.val, first.target.root.val, second.target.root.val])
    "canonical bytes retain ordered, repeated parent links"
  check (hex translated.source.val == expected) "translated native name matches independent Git fixture"
  let policy : Semantics.Prolly.Policy String := ⟨2, by decide, fun _ _ => false⟩
  for layout in [Dasl.Layout.stringList, Dasl.Layout.stringProlly policy] do
    let some alternate := translate (model algorithm layout) merge | throw (IO.userError "alternate layout")
    check (alternate.source.val == translated.source.val) "layout does not affect the native name"
    check (alternate.target.root.val != objectZero.val) "alternate layout has a serializable commit"
    check (alternate.target.root.val != translated.target.root.val) "layout affects the canonical target name"
  pure translated.target.root

private abbrev Oid := Native.NameBytes .sha1

private def fixtureBinding {kind : Kind} (node : Node String Oid kind) : IO (Oid × Binding String Oid kind) := do
  let native := (model .sha1 .dict).native
  let some bytes := node.preimage? native | throw (IO.userError "fixture cannot be serialized")
  pure (native.assign bytes, ⟨node, bytes⟩)

private def expectError {Value : Type} (result : Except (Graph.Error Oid) Value)
    (expected : Graph.Error Oid) (label : String) : IO Unit :=
  match result with
  | .error actual => check (decide (actual = expected)) label
  | .ok _ => throw (IO.userError label)

private def exerciseGraph : IO Unit := do
  let profile := model .sha1 .dict
  let external := repeated .sha1 0x77
  let payload := "shared blob\n".toByteArray
  let (blobName, blob) ← fixtureBinding (.blob payload)
  let (subtreeName, subtree) ← fixtureBinding (.tree ⟨{"shared"}, fun _ => ⟨.file .symlink, blobName⟩⟩)
  let (treeName, tree) ← fixtureBinding (.tree ⟨{"a", "dir", "sub"}, fun key =>
    if key.val = "a" then ⟨.file .executable, blobName⟩
    else if key.val = "dir" then ⟨.directory, subtreeName⟩
    else ⟨.gitlink, external⟩⟩)
  let (ancestorName, ancestor) ← fixtureBinding (.commit ⟨treeName, [], metadata "base\n"⟩)
  let (firstName, first) ← fixtureBinding (.commit ⟨treeName, [ancestorName], metadata "first\n"⟩)
  let (secondName, second) ← fixtureBinding (.commit ⟨treeName, [ancestorName], metadata "second\n"⟩)
  let (mergeName, merge) ← fixtureBinding (.commit ⟨treeName, [secondName, firstName, secondName], metadata "merge\n"⟩)
  let store : Lookup String Oid := fun
    | .blob, name => if name = blobName then .found blob else .missing
    | .tree, name => if name = treeName then .found tree else if name = subtreeName then .found subtree else .missing
    | .commit, name =>
      if name = mergeName then .found merge else if name = secondName then .found second
      else if name = firstName then .found first else if name = ancestorName then .found ancestor
      else if name = external then .invalid else .missing
  let .ok outcome := Graph.run profile store 6 .commit mergeName | throw (IO.userError "rooted graph translation")
  check (decide (outcome.completionOrder = [(.blob, blobName), (.tree, subtreeName), (.tree, treeName),
    (.commit, ancestorName), (.commit, secondName), (.commit, firstName), (.commit, mergeName)]))
    "each local node finishes once, in DFS postorder; the gitlink does not read the local store"
  check (decide (outcome.result.source = mergeName)) "the requested root name is preserved on the native side"
  let some externalTarget := profile.frontier .commit external | throw (IO.userError "fixture frontier")
  let rawTarget := namer.blob payload
  let subtreeTarget := namer.object (Dasl.dictDirectory.encode
    ⟨{"shared"}, fun _ => ⟨.file .symlink, rawTarget⟩⟩)
  let treeTarget := namer.object (Dasl.dictDirectory.encode ⟨{"a", "dir", "sub"}, fun key =>
    if key.val = "a" then ⟨.file .executable, rawTarget⟩
    else if key.val = "dir" then ⟨.directory, subtreeTarget⟩ else ⟨.gitlink, externalTarget⟩⟩)
  let targetCommit := fun parents message => (Dasl.namedCommit Dasl.metadataCodec).encode
    ⟨treeTarget, parents, profile.metadata (metadata message)⟩
  let baseTarget := namer.object (targetCommit [] "base\n")
  let firstTarget := namer.object (targetCommit [baseTarget] "first\n")
  let secondTarget := namer.object (targetCommit [baseTarget] "second\n")
  let mergeValue := targetCommit [secondTarget, firstTarget, secondTarget] "merge\n"
  let some decoded := (objectBytes? mergeValue).bind Formats.Dasl.Wire.parse? |
    throw (IO.userError "canonical merge preimage")
  let some links := (Dasl.namedCommit Dasl.metadataCodec).decode? decoded | throw (IO.userError "merge codec")
  check (decide (outcome.result.target.root = namer.object mergeValue ∧
    links.parents = [secondTarget, firstTarget, secondTarget])) "target root incorporates ordered and repeated parents"
  let events := outcome.result.trace.events.toFinset
  check (decide ((⟨.commit, external, externalTarget, none⟩ : Event Oid Cid) ∈ events ∧
    (⟨.commit, ancestorName, baseTarget, some ancestor.bytes⟩ : Event Oid Cid) ∈ events ∧
    (⟨.blob, blobName, rawTarget, some blob.bytes⟩ : Event Oid Cid) ∈ events))
    "trace retains external and shared materialized pairs with exact native bytes"
  let policy : Semantics.Prolly.Policy String := ⟨2, by decide, fun _ _ => false⟩
  let .ok prolly := Graph.run { profile with layout := .stringProlly policy } store 6 .commit mergeName |
    throw (IO.userError "rooted Prolly translation")
  check (decide (prolly.result.source = mergeName ∧ prolly.result.target.root ≠ outcome.result.target.root))
    "changing target layout changes the target name, not the source name"
  expectError (Graph.run { profile with frontier := fun _ _ => none } store 6 .commit mergeName)
    (.externalGitlink external) "unmapped gitlink"
  let allowAncestor := fun kind name =>
    if (kind, name) = (.commit, ancestorName) then some baseTarget else profile.frontier kind name
  expectError (Graph.run { profile with frontier := allowAncestor }
    (fun kind name => if (kind, name) = (.commit, ancestorName) then .missing else store kind name)
    6 .commit mergeName) (.missing (.commit, ancestorName)) "frontier mapping does not allow a missing local parent"
  expectError (Graph.run profile (fun kind name => if (kind, name) = (.tree, subtreeName) then .invalid else store kind name)
    6 .commit mergeName) (.invalid (.tree, subtreeName)) "adapter rejects invalid tree"
  expectError (Graph.run profile (fun kind name => match kind with
    | .blob => .found { blob with bytes := ByteArray.empty }
    | other => store other name) 6 .commit mergeName)
    (.invalid (.blob, blobName)) "original bytes must agree with the typed binding"
  expectError (Graph.run profile (fun kind name => match kind with
    | .commit => .found merge
    | other => store other name) 6 .commit ancestorName)
    (.invalid (.commit, ancestorName)) "native assignment must agree with the requested name"
  expectError (Graph.run profile store 2 .commit mergeName) (.fuel (.blob, blobName)) "depth bound"
  let (cycleName, cycle) ← fixtureBinding (.commit ⟨treeName, [mergeName], metadata "cycle\n"⟩)
  let assign := fun bytes => if bytes = cycle.bytes then mergeName else profile.native.assign bytes
  let cycleProfile := { profile with native := { profile.native with assign := assign } }
  let cycleStore : Lookup String Oid := fun
    | .commit, name => if name = mergeName then .found cycle else store .commit name
    | .tree, name => store .tree name
    | .blob, name => store .blob name
  check (decide (cycleName ≠ mergeName)) "cycle fixture requires an abstract, non-Git assignment"
  expectError (Graph.run cycleProfile cycleStore 6 .commit mergeName) (.cycle (.commit, mergeName)) "active-path cycle"

public def main : IO Unit := do
  let fromSHA1 ← exercise .sha1 "3c550f58242cd06b475ce597a018d2fa6889f9e6"
  let fromSHA256 ← exercise .sha256 "71d3381193ea759c83f1f2d39e6dbcdf832dbd9a0c69b7d1eeaed4f59b3cd14b"
  check (fromSHA1.val == fromSHA256.val) "for the same target graph, changing native hash does not change the target name"
  exerciseGraph
  IO.println "Git translation checks passed"

#print axioms translate
#print axioms translate_root_pair
#print axioms translate_native
#print axioms translate_commit_evidence
#print axioms Audit.sameTarget
#print axioms Plan.reaches
#print axioms Plan.accessible
#print axioms Plan.native_exact
#print axioms Outcome.rootPair
#print axioms Outcome.reaches
#print axioms Outcome.audited
#print axioms Outcome.commitEvidence
