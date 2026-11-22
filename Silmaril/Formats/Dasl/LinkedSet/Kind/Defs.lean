module

public import Silmaril.Formats.Dasl.LinkedSet.Thms

@[expose] public section

namespace Silmaril.Formats.Dasl.LinkedSet

inductive Kind where
  | objects
  | blobs
  | mixed

variable {Name Object : Type}

def Kind.allows (kind : Kind) (link : Link Name) : Bool :=
  match kind, link with
  | .objects, .obj _ | .blobs, .blob _ | .mixed, _ => true
  | _, _ => false

abbrev TypedLink (Name : Type) (kind : Kind) := {link : Link Name // kind.allows link = true}

def TypedLink.object (name : Name) : TypedLink Name .objects := ⟨.obj name, rfl⟩

def TypedLink.blob (name : Name) : TypedLink Name .blobs := ⟨.blob name, rfl⟩

def TypedLink.toMixed (kind : Kind) : TypedLink Name kind ↪ TypedLink Name .mixed :=
  ⟨fun link => ⟨link.val, rfl⟩,
    fun _ _ same => Subtype.ext (congrArg (fun link : TypedLink Name .mixed => link.val) same)⟩

def Reader.resolveTyped? (reader : Reader Object Name) {kind : Kind} (link : TypedLink Name kind) :
    Option (Item Object) := reader.resolve? link.val

/-- Uses the existing link decoder; the index adds a tag check, not a
resolution or naming policy. -/
def typedLink (kind : Kind) : Encode.TotalCodec (TypedLink Name kind) (Shallow Name) where
  encode link := Encode.link.encode link.val
  decode? tree := (Encode.link.decode? tree).bind fun link =>
    if allowed : kind.allows link = true then some ⟨link, allowed⟩ else none
  recovers link := by simp [Encode.link.recovers, link.property]

def typedLinks (kind : Kind) : Encode.TotalCodec (List (TypedLink Name kind)) (Shallow Name) :=
  Encode.listOf (typedLink kind)

/-- Keep the checked linked-set layout unchanged; only refine its link tags.
This is not an order-preservation law for renaming or changing links. -/
def matchesKind (kind : Kind) (layout : Layout Name) : Bool :=
  layout.entries.all fun entry => kind.allows entry.2

abbrev TypedLayout (Name : Type) (kind : Kind) := {layout : Layout Name // matchesKind kind layout = true}

def TypedLayout.toMixed (kind : Kind) : TypedLayout Name kind ↪ TypedLayout Name .mixed :=
  ⟨fun layout => ⟨layout.val, List.all_eq_true.mpr fun _ _ => rfl⟩,
    fun _ _ same => Subtype.ext (congrArg (fun layout : TypedLayout Name .mixed => layout.val) same)⟩

def narrow? (kind : Kind) (layout : Layout Name) : Option (TypedLayout Name kind) :=
  if allowed : matchesKind kind layout = true then some ⟨layout, allowed⟩ else none

def encodeTyped {kind : Kind} (layout : TypedLayout Name kind) : Shallow Name := encode layout.val

def decodeTyped? [DecidableEq Name] (profile : Profile Object Name) (kind : Kind) (value : Shallow Name) :
    Option (TypedLayout Name kind) := (decode? profile value).bind (narrow? kind)

end Silmaril.Formats.Dasl.LinkedSet
