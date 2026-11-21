module

public import Silmaril.Formats.Git.Dasl.Thms

@[expose] public section

namespace Silmaril.Formats.Git.Dasl

open Silmaril.Formats.Dasl
open Silmaril.Semantics (OrderedMap)

variable {Key Name : Type}

def orderedDirectory [LinearOrder Key] : Encode.TotalCodec (ShallowTree Key Name) (OrderedMap Key (Entry Name)) :=
  ⟨Directory.ordered, some ∘ Directory.ofOrdered, fun dir => congrArg some dir.ofOrdered_ordered⟩

/-- Sorted list of two-element arrays `[name, {mode, link}]`, not a list of `{k,v}` records. -/
def pairDirectory [LinearOrder Key] (key : Encode.TotalCodec Key (Shallow Name)) :
    Encode.TotalCodec (ShallowTree Key Name) (Shallow Name) :=
  orderedDirectory.then (Encode.pairMap key entryCodec)

def dictDirectory : Encode.TotalCodec (ShallowTree String Name) (Shallow Name) :=
  (⟨fun dir => ⟨dir.keys, dir.get⟩, fun fields => some ⟨fields.keys, fields.values⟩,
    fun ⟨_, _⟩ => rfl⟩ : Encode.TotalCodec (ShallowTree String Name) (Encode.Fields (Entry Name))).then
    (Encode.dictOf entryCodec)

def Layout.flat (codec : Encode.TotalCodec (ShallowTree Key Name) (Shallow Name)) : Layout Key Name :=
  ⟨fun _ dir => some (codec.encode dir, ⟨fun _ _ => False, fun _ _ => False⟩)⟩

def Layout.stringList : Layout String Name := flat (pairDirectory Encode.text)
def Layout.byteList : Layout Prolly.ByteKey Name := flat (pairDirectory Prolly.byteKey)
def Layout.dict : Layout String Name := flat dictDirectory

open Silmaril.Semantics.Prolly (Block Policy build nodeBlock blockOccurrences)

def prollyAddress (naming : Naming Name) (key : Encode.TotalCodec Key (Shallow Name)) :
    Block Name Key (Entry Name) → Name :=
  fun block => naming.object (((Prolly.blockCodec key entryCodec).encode? block).getD .null)

/-- The `.null` fallback in the total address function is unreachable for all
blocks of a successful layout. No unrenderable block is silently admitted. -/
def Layout.prolly [LinearOrder Key] (policy : Policy Key) (key : Encode.TotalCodec Key (Shallow Name)) :
    Layout Key Name where
  encode? naming dir := do
    let tree := build policy dir.ordered
    let address := prollyAddress naming key
    let codec := Prolly.blockCodec key entryCodec
    let blocks := blockOccurrences address tree.level tree.root
    if blocks.all (fun block => (codec.encode? block).isSome) then
      let root ← codec.encode? (nodeBlock address tree.level tree.root)
      pure (root, ⟨fun name value => ∃ block ∈ blocks, name = address block ∧ codec.encode? block = some value,
        fun _ _ => False⟩)
    else none

def Layout.stringProlly (policy : Policy String) : Layout String Name := prolly policy Encode.text
def Layout.byteProlly (policy : Policy Prolly.ByteKey) : Layout Prolly.ByteKey Name := prolly policy Prolly.byteKey

def Layout.utf8 (layout : Layout Prolly.ByteKey Name) : Layout String Name :=
  layout.contramap (fun dir => dir.rekey utf8KeyCodec)

def Layout.utf8List : Layout String Name := byteList.utf8
def Layout.utf8Prolly (policy : Policy Prolly.ByteKey) : Layout String Name := (byteProlly policy).utf8

end Silmaril.Formats.Git.Dasl
