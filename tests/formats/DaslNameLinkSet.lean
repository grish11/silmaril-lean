module

import Silmaril.Formats.Dasl.NameLinkSet.Compatibility.Thms
import Silmaril.Formats.Dasl.NameLinkSet.Resolved.Thms
import Silmaril.Formats.Dasl.SparseIntSet.Defs
meta import Silmaril.Formats.Dasl.NameLinkSet.Compatibility.Thms
meta import Silmaril.Formats.Dasl.NameLinkSet.Resolved.Thms
meta import Silmaril.Formats.Dasl.SparseIntSet.Defs

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.NameLinkSet Silmaril.Formats.Cbor Silmaril.Semantics

private def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def expect {Value : Type} (option : Option Value) (label : String) : IO Value :=
  match option with
  | some value => pure value
  | none => throw (IO.userError label)

private def fixtureLayout : Layout (MixedKey Nat) :=
  normalize [taggedKey (.blob 3), taggedKey (.obj 8)]

private def fixtureBytes : ByteArray := ⟨#[255, 0]⟩

private def fixtureTarget : (link : Link Nat) → Target link
  | .obj _ => .blob 2 fixtureBytes
  | .blob _ => fixtureBytes

private def fixtureView : ResolvedView mixedKey fixtureLayout :=
  fun member => fixtureTarget (mixedKey.encode member.val)

private def fixtureObject : ↥(names fixtureLayout) :=
  ⟨taggedKey (.obj 8), by simp [fixtureLayout, normalize_names]⟩

example : fixtureView.entry fixtureObject = .obj 8 (.blob 2 fixtureBytes) := rfl

example : mixedCodec.decode? fixtureView.toNamed.embed.shallow = some fixtureLayout :=
  fixtureView.recovers

private def fixtureStore : Store Nat :=
  ⟨(fun _ source => source = .ref (.blob 2)), (fun _ bytes => bytes = fixtureBytes)⟩

private theorem fixtureValid : fixtureView.ValidIn fixtureStore := by
  intro member
  change Expands fixtureStore (.ref (mixedKey.encode member.val))
    (Target.named (mixedKey.encode member.val) (fixtureTarget (mixedKey.encode member.val)))
  cases mixedKey.encode member.val with
  | obj => exact .obj rfl (.blob rfl)
  | blob => exact .blob rfl

example : Expands fixtureStore fixtureView.toNamed.embed.shallow fixtureView.toNamed := ResolvedView.expands fixtureValid

private def fixtureSorted : SortedNamed (mixedKey (Name := Nat)) := SortedNamed.ofView fixtureView

private theorem fixtureBound : fixtureStore.Binding := by
  constructor <;> intro _ _ _ leftHit rightHit <;> exact leftHit.trans rightHit.symm

example :
    let correspondence := SortedNamed.compatibleEquiv mixedKey fixtureStore fixtureBound
    let validTree := ⟨fixtureSorted, SortedNamed.valid_ofView fixtureValid⟩
    correspondence (correspondence.symm validTree) = validTree :=
  (SortedNamed.compatibleEquiv mixedKey fixtureStore fixtureBound).apply_symm_apply _

example : ¬ fixtureView.ValidIn { fixtureStore with blobs := fun _ _ => False } := by
  intro valid
  have expanded := valid fixtureObject
  change Expands _ (.ref (.obj 8)) (.obj 8 (.blob 2 fixtureBytes)) at expanded
  cases expanded with
  | obj _ child =>
    cases child with
    | blob absent => exact absent

private def sortedNamed : IO Unit := do
  check (decide (fixtureSorted.forget.keys = fixtureLayout.keys)) "named tree forget retains order"
  match fixtureSorted.lookup? (taggedKey (.obj 8)) with
  | some (.obj 8 (.blob 2 bytes)) => check (decide (bytes = fixtureBytes)) "named lookup preserves nested names"
  | _ => throw (IO.userError "missing named object")
  match fixtureSorted.lookup? (taggedKey (.blob 3)) with
  | some (.blob 3 bytes) => check (decide (bytes = fixtureBytes)) "named lookup returns raw blob"
  | _ => throw (IO.userError "missing named blob")
  let wrongKind := taggedKey (.obj 3)
  check (fixtureSorted.lookup? wrongKind).isNone "same bare name at the wrong tag is not indexed"
  check (!(index fixtureSorted.forget).contains wrongKind) "direct and indexed absence agree"

private def generic : IO Unit := do
  let tagged := normalize [taggedKey (.blob 3), taggedKey (.obj 3), taggedKey (.obj 3)]
  check (decide (links mixedKey tagged = [.obj 3, .blob 3])) "same abstract name, distinct tags"
  let lenient : Encode.TotalCodec Nat (Link Nat) :=
    ⟨Link.obj, (fun | .obj name => some name | .blob name => some name), fun _ => rfl⟩
  check ((codec lenient).decode? (linkArray.encode [.blob 3])).isNone "reject silent identity substitution"
  let layout := normalize [9, 2, 6, 4, 4, 1, 20]
  let idx := index layout
  for query in List.range 22 do
    check (idx.contains query == decide (query ∈ layout.keys)) "binary search edges and gaps"
  check (!(index (normalize ([] : List Nat))).contains 0) "empty index"

private def aliasReader : LinkedSet.Reader UInt64 Nat :=
  ⟨fun _ => some 7, fun _ => none⟩

example :
    let first : Layout (MixedKey Nat) := normalize [taggedKey (.obj 1)]
    let second : Layout (MixedKey Nat) := normalize [taggedKey (.obj 2)]
    first ≠ second ∧ contents mixedKey (readerRelation aliasReader) first =
      contents mixedKey (readerRelation aliasReader) second := by
  refine ⟨?_, ?_⟩
  · intro same
    have namesSame := congrArg names same
    simp [normalize_names, taggedKey] at namesSame
  · rw [singleton_contents, singleton_contents]
    rfl

private def compareCollections {format : Drisl.CidProfile} (wire : Wire.Profile (Drisl.Cid format))
    (primary aliasName blob : Drisl.Cid format) (raw : ByteArray)
    (readBytes : Drisl.Cid format → Option ByteArray) : IO Unit :=
  letI := cidOrder (format := format); do
  let inlineCodec : Encode.TotalCodec SparseIntSet.Layout (Shallow (Drisl.Cid format)) := SparseIntSet.codec
  let inlineSet := SparseIntSet.normalize [7, 7]
  let inlineBytes ← expect (wire.render? (inlineCodec.encode inlineSet)) "inline values encode with no link policy"
  let inlineRecovered ← expect ((wire.parse? inlineBytes).bind inlineCodec.decode?) "inline values recover without a reader"
  check (SparseIntSet.contains inlineRecovered 7 && !(SparseIntSet.contains inlineRecovered 8))
    "ordinary value membership suffices"

  let reader := LinkedSet.Reader.wire wire Encode.bits (fun name => Wire.linkSupported (.blob name)) readBytes
  let profile : LinkedSet.Profile UInt64 (Drisl.Cid format) := ⟨wire.codec Encode.bits, reader, fun
    | [0, 7] => some (.obj primary)
    | [1, 255, 0] => some (.blob blob)
    | _ => none⟩
  let contentLayout ← expect (LinkedSet.normalize? profile [.object 7, .blob raw, .object 7]) "dedup linked contents"
  check (LinkedSet.cardinality contentLayout == 2) "content codec counts object and blob values"
  let reindexed := index (ofContentLayout contentLayout)
  check (reindexed.contains (taggedKey (.obj primary)) && reindexed.contains (taggedKey (.blob blob)) &&
    !(reindexed.contains (taggedKey (.obj aliasName)))) "reindex preserves exactly the preferred links"

  let preferred := normalize [taggedKey (.obj primary)]
  let alternate := normalize [taggedKey (.obj aliasName)]
  let refs := cidWireCodec wire mixedKey
  let preferredBytes ← expect (refs.encode? preferred) "preferred link encodes"
  let alternateBytes ← expect (refs.encode? alternate) "alias also encodes as a name set"
  check (decide (preferredBytes ≠ alternateBytes)) "equal content does not reflect name layout equality"
  check (decide (((refs.decode? alternateBytes).map OrderedMap.keys) = some alternate.keys)) "preserve alias on read"
  check (((wire.parse? alternateBytes).bind (LinkedSet.decode? profile)).isNone) "content codec rejects nonpreferred alias"

private def fixtures (format : Drisl.CidProfile) (hashCode : UInt8) (profile : Wire.Profile (Drisl.Cid format)) :
    IO Unit :=
  letI := cidOrder (format := format); do
  let cid kind digest := expect ((Drisl.Cid.codec format).parse?
    ([1, kind, hashCode, 32] ++ List.replicate 32 digest)) "fixture CID"
  let primary ← cid 0x71 1
  let otherName ← cid 0x71 2
  let missing ← cid 0x71 3
  let invalid ← cid 0x71 4
  let nonmember ← cid 0x71 5
  let blob ← cid 0x55 0
  let objectWire := cidWireCodec profile objectKey
  let blobWire := cidWireCodec profile blobKey
  let mixedWire := cidWireCodec profile mixedKey
  let objects := normalize [missing, otherName, primary, primary, invalid]
  let blobs := normalize [blob, blob]
  let mixed := normalize [taggedKey (.blob blob), taggedKey (.obj invalid), taggedKey (.obj primary)]
  check (decide (objects.keys = [primary, otherName, missing, invalid])) "sort and dedup by CID"
  let objectBytes ← expect (objectWire.encode? objects) "object set encodes"
  let blobBytes ← expect (blobWire.encode? blobs) "blob set encodes"
  let mixedBytes ← expect (mixedWire.encode? mixed) "mixed set encodes"
  check (decide ((objectWire.decode? objectBytes).map OrderedMap.keys = some objects.keys)) "object recovery"
  check (decide ((blobWire.decode? blobBytes).map OrderedMap.keys = some blobs.keys)) "blob recovery"
  check (decide ((mixedWire.decode? mixedBytes).map OrderedMap.keys = some mixed.keys)) "mixed recovery"
  check ((objectWire.decode? blobBytes).isNone && (blobWire.decode? objectBytes).isNone) "reject other tag"
  check ((objectWire.encode? (normalize [blob])).isNone && (blobWire.encode? (normalize [primary])).isNone)
    "wrong CID kind cannot serialize"
  for bad in [[Link.obj otherName, .obj primary], [.obj primary, .obj primary]] do
    let badBytes ← expect (profile.render? (linkArray.encode bad)) "malformed set fixture is legal wire"
    check (objectWire.decode? badBytes).isNone "reject reverse order and duplicate names"
  let raw : ByteArray := ⟨#[255, 0]⟩
  let readBytes := fun name =>
    if name = primary ∨ name = otherName then some ⟨#[7]⟩
    else if name = blob ∨ name = invalid then some raw else none
  let read := wireReader profile Wire.linkSupported Encode.bits readBytes
  let idx := index objects
  check (decide (idx.lookup objectKey read primary = some (.found (.inl 7)))) "object positive"
  check (decide (idx.lookup objectKey read otherName = some (.found (.inl 7)))) "aliases are distinct members"
  check (decide ((index blobs).lookup blobKey read blob = some (.found (.inr raw)))) "raw blob positive"
  check (decide ((index mixed).lookup mixedKey read (taggedKey (.blob blob)) = some (.found (.inr raw)))) "mixed blob"
  check (decide (idx.lookup objectKey read missing = some .missing)) "member with missing bytes"
  check (decide (idx.lookup objectKey read invalid = some .invalid)) "member with invalid object"
  check (decide (idx.lookup objectKey read nonmember = none)) "not indexed"
  check (decide (idx.lookup objectKey (fun _ => Resolution.unresolved (Value := Unit)) primary = some .unresolved))
    "unattempted resolution"
  let semantic : Finset UInt64 := {7}
  let preferred ← expect (objectWire.encode? (ofContents (fun _ => primary) semantic)) "first policy encodes"
  let alternate ← expect (objectWire.encode? (ofContents (fun _ => otherName) semantic)) "second policy encodes"
  check (decide (preferred ≠ alternate)) "same content under two coherent choices, different wire layouts"
  compareCollections profile primary otherName blob raw readBytes

public def main : IO Unit := do
  generic
  sortedNamed
  fixtures .dasl 0x12 Wire.Profile.dasl
  fixtures .bdasl 0x1e Wire.Profile.bdasl
