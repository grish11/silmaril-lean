module

import Silmaril.Formats.Git.Arena.Graph.Thms
import Silmaril.Formats.Git.Dasl.Layouts.Defs
meta import Silmaril.Formats.Git.Arena.Defs
meta import Silmaril.Formats.Git.Arena.Graph.Defs
meta import Silmaril.Formats.Git.Dasl.Layouts.Defs
meta import Silmaril.Formats.Git.Native.Defs
meta import Silmaril.Formats.Git.Translate.Graph.Defs
meta import Silmaril.Semantics.Arena.Defs

open Silmaril.Formats.Git
open Silmaril.Formats.Git.Arena

private inductive Content where
  | file | directory | parent | root
  deriving DecidableEq

private abbrev GitName := Native.NameBytes .sha1

private def digest (byte : UInt8) : GitName :=
  ⟨⟨Array.replicate 20 byte⟩, by simp [ByteArray.size, Native.Algorithm.width]⟩

private def oid : Content → GitName
  | .file => digest 1
  | .directory => digest 2
  | .parent => digest 3
  | .root => digest 4

private def kind : Content → Kind
  | .file => .blob
  | .directory => .tree
  | .parent | .root => .commit

private def file : ByteArray := "test bytes\n".toByteArray

private def directory : ShallowTree String GitName :=
  let empty : ShallowTree String GitName := ⟨∅, fun index => False.elim (Finset.notMem_empty _ index.property)⟩
  empty.insert "example" ⟨.file .executable, oid .file⟩

private def author : Native.Person := ⟨"Tester", "test@example.org", 0⟩

private def commit (parents : List GitName) (message : String) : Commit GitName GitName Native.CommitMetadata :=
  ⟨oid .directory, parents, ⟨author, author, message⟩⟩

private def node : (kind : Kind) → Content → Option (Translate.Graph.Node String GitName kind)
  | .blob, .file => some (.blob file)
  | .tree, .directory => some (.tree directory)
  | .commit, .parent => some (.commit (commit [] "complete parent\n"))
  | .commit, .root => some (.commit (commit [oid .parent, oid .parent] "root with repeated parent\n"))
  | _, _ => none

private def preimage : Content → Option ByteArray
  | .file => some (Native.loose .blob file)
  | .directory => (Native.treePayload? (Native.nameBytesCodec .sha1) (directory.rekey Dasl.utf8KeyCodec)).map
      (Native.loose .tree)
  | .parent => Native.commitBytes? (Native.nameBytesCodec .sha1) (commit [] "complete parent\n")
  | .root => Native.commitBytes? (Native.nameBytesCodec .sha1)
      (commit [oid .parent, oid .parent] "root with repeated parent\n")

private def nameBytes (bytes : ByteArray) : GitName :=
  match ([.file, .directory, .parent, .root] : List Content).find? (fun data => decide (preimage data = some bytes)) with
  | some data => oid data
  | none => digest 0

private def arenaProfile : Arena.Profile Nat Content where
  kind content := some (kind content)
  gitBytes
    | .sha1 => preimage
    | .sha256 => fun _ => none
  gitHash
    | .sha1 => some ∘ nameBytes
    | .sha256 => fun _ => none
  casBytes := fun _ _ => none
  casName := fun _ _ => none

private def target : Translate.Profile .sha1 String GitName Nat Metadata where
  native := ⟨Dasl.utf8KeyCodec, Native.nameBytesCodec .sha1, nameBytes⟩
  naming := ⟨fun _ => 1, ByteArray.size⟩
  layout := Dasl.Layout.dict
  valid := validComponent
  metadata data := ⟨data.message.toByteArray, 0⟩
  codec := Dasl.metadataCodec
  frontier := fun _ _ => none

private abbrev TestState := State 4 Nat Content
private abbrev TestBackend := GitBackend .sha1 4 Nat Content String

private def claim (content : Content) : Arena.Id Nat := GitBackend.id .sha1 (oid content)

private def checked {Value : Type} (result : Except Arena.Fault Value) : Except String Value :=
  result.mapError fun fault => s!"unexpected arena fault: {repr fault}"

private def load (state : TestState) (key : Fin 4) (content : Content) : Except String TestState := do
  let reserved ← checked (state.step arenaProfile key (.reserve (claim content) (some (kind content))))
  let (_, loaded) ← checked (reserved.cache arenaProfile key (claim content) (fun _ => .found content))
  pure loaded

private def backend (state : TestState) (parent : Fetch Content) : TestBackend :=
  ⟨arenaProfile, state, fun id => if id = claim .parent then parent else .invalid, node⟩

private def require (message : String) (claim : Prop) [Decidable claim] : Except String Unit :=
  if claim then .ok () else .error message

private def faults (view : TestBackend) (fuel : Nat) (expected : GitBackend.Fault .sha1) : Bool :=
  match view.discover target fuel .commit (oid .root) with
  | .error fault => decide (fault = expected)
  | .ok _ => false

private def exercise : Except String Unit := do
  let empty : TestState := Silmaril.Semantics.Arena.State.empty
  let withFile ← load empty 0 .file
  let withTree ← load withFile 1 .directory
  let resident ← load withTree 2 .root
  let parentAddress : Translate.Graph.Address GitName := (.commit, oid .parent)
  require "unindexed is not remote absence" (faults (backend resident (.found .parent)) 8
    (.boundary parentAddress .unindexed) = true)
  let shallow ← checked (resident.step arenaProfile 3 (.reserve (claim .parent) (some .commit)))
  require "shallow parent remains deferred" (faults (backend shallow .deferred) 8 (.boundary parentAddress .deferred) = true)
  require "reader reports missing" (faults (backend shallow .missing) 8 (.boundary parentAddress .missing) = true)
  require "invalid fetch does not become absence" (faults (backend shallow (.found .root)) 8
    (.boundary parentAddress .invalid) = true)
  require "fuel is not a fetch boundary" (faults (backend shallow .deferred) 1 (.graph (.fuel (.tree, oid .directory))) = true)
  let .ok result := (backend shallow (.found .parent)).run target 8 .commit (oid .root) |
    .error "the indexed parent should complete via the supplied reader"
  require "root has original native name" (result.result.source = oid .root)
  require "shared tree and repeated parent complete once" (result.completionOrder =
    [(.blob, oid .file), (.tree, oid .directory), parentAddress, (.commit, oid .root)])
  require "read-through is not publication" (shallow.lookup arenaProfile (claim .parent) = .placeholder)

public def main : IO Unit :=
  match exercise with
  | .ok () => IO.println "Git arena graph checks passed"
  | .error detail => throw (IO.userError detail)

#print axioms State.resolve_found
#print axioms GitBackend.inspect_found
#print axioms GitBackend.observed_origin
#print axioms GitBackend.reaches_origin
