module

import Silmaril.Formats.Dasl.PairedShallow.Thms

namespace Silmaril.Formats.Dasl.PairedShallow

open Silmaril.Semantics.Naming

private def names (name : Bool) : Nat := if name then 3 else 2
private def objView : PairedShallow Bool Nat := ofConcrete names (.ref (.obj true))
private def blobView : PairedShallow Bool Nat := ofConcrete names (.ref (.blob false))

example : objView.concrete = .ref (.obj true) ∧ objView.abstract = .ref (.obj 3) := ⟨rfl, rfl⟩
example : blobView.concrete = .ref (.blob false) ∧ blobView.abstract = .ref (.blob 2) := ⟨rfl, rfl⟩
example : objView.AgreesBy names := ofConcrete_agrees names _
example : blobView.AgreesBy names := ofConcrete_agrees names _

private def store : Store Nat :=
  ⟨graph fun name => if name = 3 then some .null else none,
   graph fun name => if name = 2 then some ByteArray.empty else none⟩

example : objView.AbstractValid store := ⟨⟨graph_binding _, graph_binding _⟩, .obj 3 .null, .obj rfl .null⟩
example : blobView.AbstractValid store := ⟨⟨graph_binding _, graph_binding _⟩, .blob 2 ByteArray.empty, .blob rfl⟩

private def wrongLane : PairedShallow Bool Nat := .ref (.blob (true, 3))

example : wrongLane.AgreesBy names := ofConcrete_agrees names (.ref (.blob true))
example : ¬ wrongLane.AbstractValid store := by
  intro ⟨_, _, expanded⟩
  cases expanded with
  | blob hit => contradiction

private def mismatched : PairedShallow Bool Nat := .ref (.blob (true, 2))

example : ¬ mismatched.AgreesBy names := by
  intro agrees
  have impossible : (Link.blob 3 : Link Nat) = .blob 2 := agrees (link := .blob (true, 2)) rfl
  cases impossible

end Silmaril.Formats.Dasl.PairedShallow
