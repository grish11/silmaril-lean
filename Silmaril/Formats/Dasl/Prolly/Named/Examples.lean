module

import Silmaril.Formats.Dasl.Prolly.Named.Thms
import all Silmaril.Formats.Dasl.Prolly.Thms

namespace Silmaril.Formats.Dasl.Prolly.NamedExamples

open Silmaril.Semantics
open Silmaril.Semantics.Prolly

private def root : Silmaril.Semantics.Prolly.Tree (Link Nat) Unit :=
  ⟨1, [(.obj 7, [(.obj 7, ())]), (.blob 7, [(.blob 7, ())])]⟩

private def address : Block Nat (Link Nat) Unit → Nat
  | .leaf [(.obj _, _)] => 20
  | .leaf _ => 21
  | .branch _ _ => 22

private def codec := blockCodec (Name := Nat) Encode.link Encode.null

private def object? : Nat → Option (Shallow Nat)
  | 7 => some .null
  | 20 => codec.encode? (.leaf [(.obj 7, ())])
  | 21 => codec.encode? (.leaf [(.blob 7, ())])
  | 22 => codec.encode? (nodeBlock address root.level root.root)
  | _ => none

private def store (hasBlob : Bool) : Store Nat :=
  ⟨Naming.graph object?, fun name bytes => hasBlob = true ∧ name = 7 ∧ bytes = ByteArray.empty⟩

private theorem stored (hasBlob : Bool) : Stored codec address root (store hasBlob) := by
  intro block member
  change block ∈ [nodeBlock address root.level root.root, .leaf [(.obj 7, ())], .leaf [(.blob 7, ())]] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals exact ⟨_, rfl, rfl⟩

private theorem objectReady : ExpansionReady (store true) (.ref (.obj 7)) :=
  ⟨Value.obj .null, .obj .null (show object? 7 = some .null from rfl)⟩

private theorem blobReady : ExpansionReady (store true) (.ref (.blob 7)) :=
  ⟨Value.blob ByteArray.empty, .blob ⟨rfl, rfl, rfl⟩⟩

private theorem ready : NodeReady Encode.link Encode.null (store true) root.level root.root := by
  change ∀ row ∈ [(Link.obj 7, [(Link.obj 7, ())]), (Link.blob 7, [(Link.blob 7, ())])], _
  intro row member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨objectReady, fun _ member => (List.mem_singleton.mp member).symm ▸ ⟨objectReady, ⟨_, .null⟩⟩⟩
  · exact ⟨blobReady, fun _ member => (List.mem_singleton.mp member).symm ▸ ⟨blobReady, ⟨_, .null⟩⟩⟩

example : ∃ named, FullNames (store true) 22 named :=
  let ⟨named, _, handled⟩ := (stored true).namedRoot ready
  ⟨named, handled⟩

example : Stored codec address root (store false) ∧ ¬ ExpansionReady (store false) (.ref (.blob 7)) := by
  refine ⟨stored false, ?_⟩
  rintro ⟨_, choices⟩
  cases choices with
  | blob present => exact Bool.false_ne_true present.1

end Silmaril.Formats.Dasl.Prolly.NamedExamples
