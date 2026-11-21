module

public import Mathlib.Data.Multiset.Bind
public import Silmaril.Formats.Git.Native.Defs

/-! A bottom-up interpretation of a finite Git unfolding. The two sides name
different preimages; a typed correspondence, not digest equality, connects them. -/

@[expose] public section

namespace Silmaril.Formats.Git.Translate

open Silmaril.Formats.Dasl (Shallow)
open Silmaril.Formats.Dasl.Encode (TotalCodec)
open Silmaril.Semantics

variable {Key Source Target Meta : Type} {algorithm : Native.Algorithm}

abbrev Correspondence (Source Target : Type) := Kind → Naming.Relation Source Target

/-- Repeated occurrences of a source name of the same kind must agree on its
target name. This does not assert injectivity or resolve an opaque reference. -/
def Correspondence.Functional (rel : Correspondence Source Target) : Prop :=
  ∀ kind, Naming.Binding (rel kind)

/-- Each finite trace occurrence has a typed name pair and either its native
preimage or an opaque cut (no assertion of object availability). -/
structure Event (Source Target : Type) where
  kind : Kind
  source : Source
  target : Target
  bytes : Option ByteArray
  deriving DecidableEq

structure Trace (Source Target : Type) where
  events : Multiset (Event Source Target)

def Trace.opaque (kind : Kind) (source : Source) (target : Target) : Trace Source Target :=
  ⟨{⟨kind, source, target, none⟩}⟩

def Trace.observe (kind : Kind) (source : Source) (target : Target) (bytes : ByteArray) : Trace Source Target :=
  ⟨{⟨kind, source, target, some bytes⟩}⟩

def Trace.union (left right : Trace Source Target) : Trace Source Target := ⟨left.events + right.events⟩

def Trace.collect {Index : Type} [Fintype Index] (items : Index → Trace Source Target) : Trace Source Target :=
  ⟨Multiset.bind (Finset.univ : Finset Index).val (fun index => (items index).events)⟩

def Trace.pairs (trace : Trace Source Target) : Correspondence Source Target :=
  fun kind source target => ∃ bytes, ⟨kind, source, target, bytes⟩ ∈ trace.events

def Trace.preimages (trace : Trace Source Target) : Kind → Naming.Relation Source ByteArray :=
  fun kind source bytes => ∃ target, ⟨kind, source, target, some bytes⟩ ∈ trace.events

def Trace.frontier (trace : Trace Source Target) : Correspondence Source Target :=
  fun kind source target => ⟨kind, source, target, none⟩ ∈ trace.events

def Trace.Closed (trace : Trace Source Target) : Prop := ∀ kind source target, ¬ trace.frontier kind source target

structure Profile (algorithm : Native.Algorithm) (Key Source Target Meta : Type) where
  native : Native.Profile algorithm Key Source
  naming : Dasl.Naming Target
  layout : Dasl.Layout Key Target
  valid : Key → Bool
  metadata : Native.CommitMetadata → Meta
  codec : TotalCodec Meta (Shallow Target)
  frontier : Kind → Source → Option Target

structure Result (Source Target : Type) where
  source : Source
  target : Dasl.Rendered Target
  trace : Trace Source Target

def Result.RootPair (kind : Kind) (result : Result Source Target) : Prop :=
  result.trace.pairs kind result.source result.target.root

def Result.SourceWitness (assign : ByteArray → Source) (kind : Kind) (result : Result Source Target)
    (view : Native.View Source) : Prop :=
  view.target assign = result.source ∧ match view with
    | .opaque name => result.trace.frontier kind name result.target.root
    | .encoded bytes => result.trace.preimages kind result.source bytes

/-- The target serializer may be partial (e.g. `Dasl.Wire.Serializes`). The raw
blob preimage is its actual payload. Independent naming relations validate the
names provisionally used by `Profile.naming`, including names inside layouts. -/
structure Wire (Target : Type) where
  serializes : Shallow Target → ByteArray → Prop
  objects : Naming.Relation Target ByteArray
  blobs : Naming.Relation Target ByteArray

def Wire.ofFunctions (serialize? : Shallow Target → Option ByteArray) (objectName blobName : ByteArray → Target) :
    Wire Target :=
  ⟨fun value bytes => serialize? value = some bytes, fun name bytes => objectName bytes = name,
    fun name bytes => blobName bytes = name⟩

def Wire.Agrees (wire : Wire Target) (rendered : Dasl.Rendered Target) : Prop :=
  (∀ name value, rendered.store.objects name value → ∃ bytes, wire.serializes value bytes ∧ wire.objects name bytes) ∧
  Naming.Subset rendered.store.blobs wire.blobs

/-- Acceptance evidence, not an executable verifier. `observed` can be the
graph of a lookup of actual native preimages. Differences from the restricted
native renderer then fail the containment check; they are not normalized away. -/
structure Audit (result : Result Source Target) (observed : Kind → Naming.Relation Source ByteArray)
    (nativeNames : Naming.Relation Source ByteArray) (wire : Wire Target)
    (allowedFrontier : Correspondence Source Target) : Prop where
  observedBytes : ∀ kind, Naming.Subset (result.trace.preimages kind) (observed kind)
  nativeNamed : ∀ kind, Naming.Subset (result.trace.preimages kind) nativeNames
  targetWire : wire.Agrees result.target
  sharing : result.trace.pairs.Functional
  frontierAllowed : ∀ kind, Naming.Subset (result.trace.frontier kind) (allowedFrontier kind)

def materialize (assign : ByteArray → Source) (kind : Kind) (bytes : ByteArray)
    (target : Dasl.Rendered Target) (children : Trace Source Target) : Result Source Target :=
  let source := assign bytes
  ⟨source, target, (Trace.observe kind source target.root bytes).union children⟩

def Result.nativeCommit (tree : Result Source Target) (parents : List (Result Source Target))
    (metadata : Native.CommitMetadata) : Commit Source Source Native.CommitMetadata :=
  ⟨tree.source, parents.map Result.source, metadata⟩

def Result.targetCommit (profile : Profile algorithm Key Source Target Meta) (tree : Result Source Target)
    (parents : List (Result Source Target)) (metadata : Native.CommitMetadata) : Commit Target Target Meta :=
  ⟨tree.target.root, parents.map (fun parent => parent.target.root), profile.metadata metadata⟩

/-- A local commit certificate: the original bytes and target bytes are checked
separately, and the commit's direct dependencies carry the typed correspondence. -/
structure CommitEvidence (profile : Profile algorithm Key Source Target Meta) (tree : Result Source Target)
    (parents : List (Result Source Target)) (metadata : Native.CommitMetadata) (result : Result Source Target)
    (observed : Kind → Naming.Relation Source ByteArray) (nativeNames : Naming.Relation Source ByteArray)
    (wire : Wire Target) : Prop where
  root : result.RootPair .commit
  treeEdge : result.trace.pairs .tree tree.source tree.target.root
  parentEdges : ∀ parent ∈ parents, result.trace.pairs .commit parent.source parent.target.root
  sourceBytes : ∃ bytes, Native.commitBytes? profile.native.names (tree.nativeCommit parents metadata) = some bytes ∧
    observed .commit result.source bytes ∧ nativeNames result.source bytes
  targetBytes : let codec := Dasl.namedCommit profile.codec
    let named := tree.targetCommit profile parents metadata
    let value := codec.encode named
    (codec.decode? value = some named) ∧
      ∃ bytes, result.target.store.objects result.target.root value ∧
        wire.serializes value bytes ∧ wire.objects result.target.root bytes

def commitStep (profile : Profile algorithm Key Source Target Meta) (tree : Result Source Target)
    (parents : List (Result Source Target)) (metadata : Native.CommitMetadata) : Option (Result Source Target) := do
  let bytes ← Native.commitBytes? profile.native.names (tree.nativeCommit parents metadata)
  let target := Dasl.renderCommit profile.naming profile.codec tree.target (parents.map Result.target)
    (profile.metadata metadata)
  pure (materialize profile.native.assign .commit bytes target
    (tree.trace.union (Trace.collect (Result.trace ∘ parents.get))))

def treeStep [DecidableEq Key] (profile : Profile algorithm Key Source Target Meta) (keys : Finset Key)
    (modes : ↥keys → EntryMode) (children : ↥keys → Result Source Target) : Option (Result Source Target) := do
  let nativeDir : ShallowTree Key Source := ⟨keys, fun key => ⟨modes key, (children key).source⟩⟩
  let payload ← Native.treePayload? profile.native.names (nativeDir.rekey profile.native.key)
  let target ← Dasl.renderDir profile.naming profile.layout profile.valid keys modes
    (fun key => some (children key).target)
  pure (materialize profile.native.assign .tree (Native.loose .tree payload) target
    (Trace.collect (Result.trace ∘ children)))

/-- Visit each expanded occurrence bottom-up. All tree children and ordered
commit parents are translated before hashing their enclosing object. A missing
frontier mapping rejects the input. This is not name-store traversal or cycle
detection: recursive cycles cannot be supplied except as opaque cuts. -/
def translate [DecidableEq Key] (profile : Profile algorithm Key Source Target Meta) :
    {kind : Kind} → Object Key Source Native.CommitMetadata kind → Option (Result Source Target)
  | _, .ref kind source => do
    let target ← profile.frontier kind source
    pure ⟨source, Dasl.Rendered.opaque target, Trace.opaque kind source target⟩
  | _, .blob bytes => some (materialize profile.native.assign .blob (Native.loose .blob bytes)
      (Dasl.Rendered.raw profile.naming bytes) (Trace.collect (Index := Empty) Empty.elim))
  | _, .tree keys modes children =>
    let results := fun key => translate profile (children key)
    if present : ∀ key (hit : key ∈ keys), (results ⟨key, hit⟩).isSome = true then
      treeStep profile keys modes (fun key => (results key).get (present key.val key.property))
    else none
  | _, .commit tree _ parents metadata => do
    let root ← translate profile tree
    let ancestors ← (List.ofFn (fun index => translate profile (parents index))).mapM id
    commitStep profile root ancestors metadata

end Silmaril.Formats.Git.Translate
