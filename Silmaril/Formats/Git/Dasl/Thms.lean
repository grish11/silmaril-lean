module

public import Silmaril.Formats.Git.Dasl.Defs
public import Silmaril.Formats.Git.Thms
import Silmaril.Proofs.Formats.Git.Dasl

public section

namespace Silmaril.Formats.Git

namespace Directory

variable {Key Item : Type} [LinearOrder Key]

@[simp] theorem lookup_ordered (dir : Directory Key Item) (key : Key) :
    dir.ordered.lookup? key = dir.lookup key := Proofs.Formats.Git.ordered_lookup dir key

@[simp] theorem lookup_ofOrdered (dir : Semantics.OrderedMap Key Item) (key : Key) :
    (ofOrdered dir).lookup key = dir.lookup? key := Proofs.Formats.Git.ofOrdered_lookup dir key

@[simp] theorem ofOrdered_ordered (dir : Directory Key Item) : ofOrdered dir.ordered = dir :=
  eq_of_lookup (fun key => by simp)

@[simp] theorem ordered_ofOrdered (dir : Semantics.OrderedMap Key Item) : (ofOrdered dir).ordered = dir :=
  Semantics.OrderedMap.eq_of_lookup (fun key => by simp)

end Directory

namespace Dasl

open Silmaril.Formats.Dasl

variable {Name Meta : Type}

def entryCodec : Encode.TotalCodec (Entry Name) (Shallow Name) :=
  ⟨encodeEntry, decodeEntry, Proofs.Formats.Git.entry_roundtrip⟩

def utf8KeyCodec : Encode.TotalCodec String Prolly.ByteKey :=
  ⟨utf8Key, decodeUtf8Key, Proofs.Formats.Git.utf8_roundtrip⟩

theorem linkedEntry_compatible (entry : Entry Name) : compatible (linkedEntry entry) := ⟨entry.target, rfl⟩

@[simp] theorem linkFor_map {Other : Type} (kind : Kind) (rename : Name → Other) (name : Name) :
    (linkFor kind name).map rename = linkFor kind (rename name) := by cases kind <;> rfl

theorem Rendered.opaque_materializes (kind : Kind) (name : Name) :
    (Rendered.opaque name).materializes kind (.ref (linkFor kind name)) :=
  ⟨rfl, by constructor <;> intro _ _ impossible <;> exact impossible.elim⟩

@[simp] theorem renderObject_toObject (naming : Naming Name) (layout : Layout String Name)
    (codec : Encode.TotalCodec Meta (Shallow Name)) (tree : Git.Tree) :
    renderObject naming layout validComponent codec tree.toObject = renderTree naming layout tree :=
  Proofs.Formats.Git.render_embedding naming layout codec tree

theorem names_toObject (naming : Naming Name) (layout : Layout String Name)
    (codec : Encode.TotalCodec Meta (Shallow Name)) :
    Rendered.names (fun tree : Git.Tree => renderObject naming layout validComponent codec tree.toObject) =
      Rendered.names (renderTree naming layout) := by
  unfold Rendered.names; simp only [renderObject_toObject]

end Dasl
end Silmaril.Formats.Git
